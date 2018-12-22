{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope (Scope(..), fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Monad (guard)
import Control.Monad.State (MonadState, evalState, gets, modify)
import Control.Monad.Trans (lift)
import Control.Monad.Writer.Strict (WriterT(..), runWriterT)
import Data.DList (DList)
import Data.Functor.Apply ((<.>))
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (Ap(..))
import Data.Set (Set)
import Data.Sequence (Seq, ViewL(..))

import qualified Data.Church.Maybe as Church
import qualified Data.DList as DList
import qualified Data.Set as Set
import qualified Data.Sequence as Seq

import LambdaPi
import Supply.Class

data Solution a b = Solution a (Tm (Meta a b))

type TmM a b = Tm (Meta a b)

occurs :: forall a b. (Eq a, Eq b) => a -> TmM a b -> Bool
occurs a tm =
  case tm of
    Var{} -> go False False tm
    Fst{} -> go False False tm
    Snd{} -> go False False tm
    Lam s -> go False False (sequenceA <$> fromScope s)
    Pair b c -> go False False b || go False False c
    Neutral (Var (M _)) cs -> any (go True False) cs
    Neutral (Var (N _)) cs -> any (go False True) cs
    Neutral _ cs -> any (go False False) cs
  where
    isVar Var{} = True
    isVar _ = False

    go :: forall c. (Eq a, Eq c) => Bool -> Bool -> TmM a c -> Bool
    go _ _ (Var (M b)) = a == b
    go _ _ (Var (N _)) = False
    go _ _ Fst{} = False
    go _ _ Snd{} = False
    go inMeta inVar (Lam s) = go inMeta inVar (sequenceA <$> fromScope s)
    go inMeta inVar (Pair d e) = go inMeta inVar d || go inMeta inVar e
    go inMeta inVar (Neutral (Var (M b)) cs)
      | a == b =
        if inVar
        then any ((||) <$> isVar <*> go True False) cs
        else
          if inMeta
          then any (go True False) cs
          else True
      | otherwise = any (go True False) cs
    go _ _ (Neutral (Var (N _)) cs) = any (go False True) cs
    go _ _ (Neutral _ cs) = any (go False False) cs

ex1 :: Bool
ex1 =
  occurs "alpha" $
  Var (N "x") .@ (Var (M "alpha") .@ Var (N "x"))

ex2 :: Bool
ex2 =
  occurs "beta" $
  Var (N "x") .@ (Var (M "beta") .@ lam (N "x") (Var $ N "x"))

-- |
-- Determine whether the container is comprised of distinct variables,
-- and if that set of variables contains all the variables present in another term
--
-- @O(n * log(n))@
distinctVarsContaining
  :: forall t a b
   . (Traversable t, Ord b)
  => t (TmM a b)
  -> TmM a b
  -> Maybe [b]
distinctVarsContaining tms tm =
  fmap DList.toList $
  evalState
    (do
        res <- getAp $ foldMap (Ap . go) tms
        isContained <- gets (contained `Set.isSubsetOf`)
        pure $ if isContained then res else Nothing)
    Set.empty
  where
    contained =
      foldr
        (\a b ->
           case a of
             M{} -> b
             N a' -> Set.insert a' b)
        Set.empty
        tm

    go
      :: (MonadState (Set b) m, Ord b)
      => TmM a b
      -> m (Maybe (DList b))
    go (Var a) =
      case a of
        M{} -> pure Nothing
        N b -> do
          res <- gets $ Set.member b
          if res
            then pure Nothing
            else Just (DList.singleton b) <$ modify (Set.insert b)
    go _ = pure Nothing

-- | Compute a term that solves a flex-flex equation by intersection
--
-- @O(n^2)@
intersect
  :: forall a b
   . (Eq a, Eq b)
  => Seq (TmM a b)
  -> Seq (TmM a b)
  -> Maybe (a -> TmM a b)
intersect l m =
  -- use a church-encoded maybe for proper tail recursion
  Church.maybe Nothing Just $
  (\f -> f . Var . M) <$> go l m
  where
    go
      :: forall c
       . Seq (Tm (Meta a b))
      -> Seq (Tm (Meta a b))
      -> Church.Maybe (Tm c -> Tm c)
    go a b =
      case (Seq.viewl a, Seq.viewl b) of
        (EmptyL, EmptyL) -> Church.just id
        (Var (N x) :< xs, Var (N y) :< ys) ->
          if x == y

          -- The two varables agree
                  -- O(n) (?)
          then (\f xx -> Lam $ Scope $ f $ fmap (F . Var) xx .@ Var (B ())) <$> go xs ys

          -- The two variables disagree, so the solution ignores them
                  -- O(1)
          else (\f -> Lam . lift . f) <$> go xs ys
        _ -> Church.nothing

ex3 :: TmM String String
ex3 = res "alpha"
  where
    Just res =
      intersect
        [Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y")]

ex4 :: TmM String String
ex4 = res "alpha"
  where
    Just res =
      intersect
        [Var (N "x"), Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex5 :: TmM String String
ex5 = res "alpha"
  where
    Just res =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex6 :: TmM String String
ex6 = res "alpha"
  where
    Just res =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "y"), Var (N "y"), Var (N "z")]

-- | Build a lambda that prunes out of scope variables
--
-- @O(n^2)@
pruneArgs
  :: forall a b
   . Ord b
  => Set b
  -> Seq (TmM a b)
  -> (a -> TmM a b)
pruneArgs keep tm = go tm . Var . M
  where
    go
      :: forall c
       . Seq (Tm (Meta a b))
      -> (Tm c -> Tm c)
    go a =
      case Seq.viewl a of
        EmptyL -> id
        Var (N x) :< xs ->
          if x `Set.member` keep

          then \xx -> Lam $ Scope $ go xs $ fmap (F . Var) xx .@ Var (B ())

          else Lam . lift . go xs

prune
  :: forall a b
   . Ord b
  => Set b
  -> TmM a b
  -> Maybe (TmM a b, NonEmpty (Solution a b))
prune keep =
  runWriterT .
  go (\x -> x <$ guard (Set.member x keep))
  where
    go
      :: forall c
       . (c -> Maybe b)
      -> TmM a c
      -> WriterT (NonEmpty (Solution a b)) Maybe (TmM a c)
    go _ Var{} = WriterT Nothing
    go ctx (Lam s) =
      Lam . toScope . fmap metaVar <$>
      go (unvar (const Nothing) ctx) (sequenceA <$> fromScope s)
    go ctx (Pair a b) = Pair <$> go ctx a <.> go ctx b
    go _ Fst = WriterT Nothing
    go _ Snd = WriterT Nothing
    go ctx (Neutral (Var (M a)) xs) = _
    go ctx (Neutral (Var (N a)) xs) = _

data Result a b
  = Postpone
  | Failure
  | Success (Maybe (Solution a b), Maybe (TmM a b))

solve
  :: (Eq a, Ord b, MonadSupply a m)
  => TmM a b
  -> TmM a b
  -> m (Result a b)
solve (Neutral (Var (M a)) xs) (Neutral (Var (M b)) ys)
  | a == b
  , Just tm <- intersect xs ys = do
      mv <- fresh
      pure $ Success (Just $ Solution a $ tm mv, Nothing)
  | otherwise = _
solve (Neutral (Var (M a)) xs) y
  | occurs a y = pure Failure
  | Just vars <- distinctVarsContaining xs y =
      pure $
      Success
      ( Just . Solution a $ foldr (lam . N) y vars
      , Nothing
      )
  | otherwise = pure Postpone
solve x (Neutral (Var (M b)) ys) = solve (Neutral (Var (M b)) ys) x
solve a b =
  pure $
  if a == b
  then Success (Nothing, Nothing)
  else Failure
