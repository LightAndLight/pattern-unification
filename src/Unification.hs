{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope (fromScope)
import Control.Monad.State (MonadState, evalState, gets, modify)
import Control.Monad.Trans (lift)
import Data.DList (DList)
import Data.Monoid (Ap(..))
import Data.Set (Set)
import Data.Sequence (Seq, ViewL(..))

import qualified Data.DList as DList
import qualified Data.Set as Set
import qualified Data.Sequence as Seq

import LambdaPi

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
intersect = go id
  where
    go
      :: ((a -> TmM a b) -> a -> TmM a b)
      -> Seq (TmM a b)
      -> Seq (TmM a b)
      -> Maybe (a -> TmM a b)
    go f a b =
      case (Seq.viewl a, Seq.viewl b) of
        (EmptyL, EmptyL) -> Just $ f (Var . M)
        (Var (N x) :< xs, Var (N y) :< ys) ->
          if x == y

          -- The two varables agree
                  -- O(n) (?)
          then go (\ff -> f $ \m -> lam (N x) $ ff m .@ Var (N x)) xs ys

          -- The two variables disagree, so the solution ignores them
                  -- O(1)
          else go (\ff -> f $ Lam . lift . ff) xs ys
        _ -> Nothing

ex3 :: TmM String String
ex3 = res "alpha"
  where
    Just res = intersect [Var (N "x"), Var (N "x")] [Var (N "x"), Var (N "y")]

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

data Result a b
  = Postpone
  | Failure
  | Success (Maybe (Solution a b), Maybe (TmM a b))

{-
solve :: (Eq a, Ord b) => TmM a b -> TmM a b -> Result a b
solve (Neutral (Var (M a)) xs) (Neutral (Var (M b)) ys)
  | a == b
  , Just tm <- intersect xs ys = _
  | otherwise = _
solve (Neutral (Var (M a)) xs) y
  | occurs a y = Failure
  | Just vars <- distinctVarsContaining xs y =
    Success
    ( Just . Solution a $ foldr (lam . N) y vars
    , Nothing
    )
  | otherwise = Postpone
solve x (Neutral (Var (M b)) ys) = solve (Neutral (Var (M b)) ys) x
solve a b =
  if a == b
  then Success (Nothing, Nothing)
  else Failure
-}
