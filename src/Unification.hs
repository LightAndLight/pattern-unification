{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope (Scope(..), fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Applicative (empty)
import Control.Monad (guard)
import Control.Monad.State (MonadState, evalState, gets, modify)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Control.Monad.Writer.Strict (WriterT(..), runWriterT, tell)
import Data.Bifunctor (bimap)
import Data.DList (DList)
import Data.Monoid (Ap(..))
import Data.Set (Set)
import Data.Sequence (Seq, ViewL(..))
import Data.Void (Void, absurd)
import Text.PrettyPrint.ANSI.Leijen (Doc, Pretty(..))

import qualified Data.Church.Maybe as Church
import qualified Data.DList as DList
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Text.PrettyPrint.ANSI.Leijen as Print

import LambdaPi
import Supply.Class

data Solution a b = Solution a (Tm (Meta a b))
  deriving (Eq, Show)

prettySolution :: (a -> Doc) -> (b -> Doc) -> Solution a b -> Doc
prettySolution aDoc bDoc (Solution a b) =
  Print.hsep
    [ Print.char '?' <> aDoc a
    , Print.text ":="
    , prettyTm (prettyMeta aDoc bDoc) b
    ]

instance (Pretty a, Pretty b) => Pretty (Solution a b) where
  pretty = prettySolution pretty pretty

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
  -> Maybe (a -> TmM a b, a -> TmM a b)
intersect l m =
  -- use a church-encoded maybe for proper tail recursion
  Church.maybe Nothing Just $
  bimap (\f -> f . Var . M) (\f -> f . Var . M) <$> go l m
  where
    go
      :: forall c
       . Seq (Tm (Meta a b))
      -> Seq (Tm (Meta a b))
      -> Church.Maybe (Tm c -> Tm c, Tm (Meta a b) -> Tm (Meta a b))
    go a b =
      case (Seq.viewl a, Seq.viewl b) of
        (EmptyL, EmptyL) -> Church.just (id, id)
        (Var (N x) :< xs, Var (N y) :< ys) ->
          if x == y

          -- The two varables agree
                  -- O(n) (?)
          then
            bimap
              (\f xx -> Lam $ Scope $ f $ fmap (F . Var) xx .@ Var (B ()))
              (\f xx -> f $ xx .@ Var (N x)) <$>
            go xs ys

          -- The two variables disagree, so the solution ignores them
                  -- O(1)
          else
            bimap
              (\f -> Lam . lift . f)
              id <$>
            go xs ys
        _ -> Church.nothing

ex3 :: (TmM String String, TmM String String)
ex3 = (res "alpha", res' "alpha")
  where
    Just (res, res') =
      intersect
        [Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y")]

ex4 :: (TmM String String, TmM String String)
ex4 = (res "alpha", res' "alpha")
  where
    Just (res, res') =
      intersect
        [Var (N "x"), Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex5 :: (TmM String String, TmM String String)
ex5 = (res "alpha", res' "alpha")
  where
    Just (res, res') =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex6 :: (TmM String String, TmM String String)
ex6 = (res "alpha", res' "alpha")
  where
    Just (res, res') =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "y"), Var (N "y"), Var (N "z")]

pruneArgs
  :: forall a b
    . (b -> Maybe b)
  -> Seq (TmM a b)
  -> Maybe (a -> TmM a Void, a -> TmM a b)
pruneArgs ctx =
  Church.maybe Nothing Just .
  fmap (bimap (. (Var . M)) (. (Var . M))) .
  go
  where
    go
      :: forall c
       . Seq (TmM a b)
      -> Church.Maybe (Tm c -> Tm c, TmM a b -> TmM a b)
    go a =
      case Seq.viewl a of
        EmptyL -> Church.just (id, id)
        x :< xs ->
          case x of
            Var (N b) ->
              case ctx b of
                Nothing ->
                  bimap
                    (\f xx -> Lam $ lift $ f xx)
                    id <$>
                  go xs
                Just{} ->
                  bimap
                    (\f xx -> Lam $ Scope $ f $ fmap (F . Var) xx .@ Var (B ()))
                    (\f xx -> f $ xx .@ x) <$>
                  go xs
            _ -> Church.nothing

prune
  :: forall a b m
   . (Ord b, MonadSupply a m)
  => Set b
  -> TmM a b
  -> m (Maybe (TmM a b, [Solution a b]))
prune keep =
  runMaybeT .
  runWriterT .
  go False (\x -> x <$ guard (Set.member x keep))
  where
    go
      :: forall c
       . Bool
      -> (c -> Maybe c)
      -> TmM a c
      -> WriterT [Solution a b] (MaybeT m) (TmM a c)
    go _ _ (Var v) = pure $ Var v
    go underMeta ctx (Lam s) = do
      s' <-
        go underMeta (unvar (\() -> Just (B ())) (fmap F . ctx)) $
        sequenceA <$> fromScope s
      pure $ Lam . toScope $ fmap metaVar s'
    go underMeta ctx (Pair a b) = do
      a' <- go underMeta ctx a
      b' <- go underMeta ctx b
      pure $ Pair a' b'
    go _ _ e@Fst = pure e
    go _ _ e@Snd = pure e
    go underMeta ctx (Neutral (Var (M a)) xs) = do
      xs' <- traverse (go True ctx) xs
      if not underMeta
        then
          case pruneArgs ctx xs' of
            Nothing -> empty
            Just (sol, tm') -> do
              v <- lift $ lift fresh
              tell [Solution a $ fmap absurd <$> sol v]
              pure $ tm' v
        else empty
    go underMeta ctx (Neutral a xs) = do
      xs' <- traverse (go underMeta ctx) xs
      pure $ Neutral a xs'

varSet :: Ord b => Seq (TmM a b) -> Maybe (Set b)
varSet = Church.maybe Nothing Just . go
  where
    go x =
      case Seq.viewl x of
        EmptyL -> Church.just mempty
        Var (N a) :< xs -> Set.insert a <$> go xs
        _ -> Church.nothing

data Result a b
  = Postpone
  | Failure
  | Success [Solution a b] (Maybe (TmM a b))

solve
  :: (Eq a, Ord b, MonadSupply a m)
  => TmM a b
  -> TmM a b
  -> m (Result a b)
solve (Neutral (Var (M a)) xs) tm@(Neutral (Var (M b)) ys)
  | a == b
  , Just (sol, tm') <- intersect xs ys = do
      mv <- fresh
      pure $ Success [Solution a $ sol mv] (Just $ tm' mv)
  | Just keep <- varSet xs = do
      res <- prune keep tm
      pure $ maybe Postpone (\(tm', sol) -> Success sol $ Just tm') res
  | otherwise = pure Postpone
solve (Neutral (Var (M a)) xs) y
  | occurs a y = pure Failure
  | Just vars <- distinctVarsContaining xs y =
      pure $
      Success [Solution a $ foldr (lam . N) y vars] Nothing
  | Just keep <- varSet xs = do
      res <- prune keep y
      pure $ maybe Postpone (\(tm, sol) -> Success sol $ Just tm) res
  | otherwise = pure Postpone
solve x (Neutral (Var (M b)) ys) = solve (Neutral (Var (M b)) ys) x
solve a b =
  pure $
  if a == b
  then Success [] Nothing
  else Failure
