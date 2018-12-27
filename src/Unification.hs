{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope (Scope(..), fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Applicative (empty)
import Control.Monad (guard)
import Control.Monad.State (MonadState, evalState, gets, modify)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Control.Monad.Writer.Strict (WriterT(..), runWriterT, tell)
import Data.Bifunctor (bimap)
import Data.DList (DList)
import Data.Foldable (toList)
import Data.Monoid (Ap(..))
import Data.Set (Set)
import Data.Sequence (Seq, ViewL(..))
import Data.Void (Void, absurd)
import Text.PrettyPrint.ANSI.Leijen (Doc, Pretty(..))

import qualified Data.Church.Either as Church
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
    Neutral (Var (L _)) cs -> any (go False True) cs
    Neutral (Var (R _)) cs -> any (go False True) cs
    Neutral _ cs -> any (go False False) cs
  where
    isVar Var{} = True
    isVar _ = False

    go :: forall c. (Eq a, Eq c) => Bool -> Bool -> TmM a c -> Bool
    go _ _ (Var (M b)) = a == b
    go _ _ (Var (N _)) = False
    go _ _ (Var (L _)) = False
    go _ _ (Var (R _)) = False
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
    go _ _ (Neutral (Var (L _)) cs) = any (go False True) cs
    go _ _ (Neutral (Var (R _)) cs) = any (go False True) cs
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
   . (Traversable t, Ord a, Ord b)
  => t (TmM a b)
  -> TmM a b
  -> Maybe [Meta a b]
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
             a' -> Set.insert a' b)
        Set.empty
        tm

    go
      :: (MonadState (Set (Meta a b)) m, Ord b)
      => TmM a b
      -> m (Maybe (DList (Meta a b)))
    go (Var a) =
      case a of
        M{} -> pure Nothing
        b -> do
          res <- gets $ Set.member b
          if res
            then pure Nothing
            else Just (DList.singleton b) <$ modify (Set.insert b)
    go _ = pure Nothing

data IntersectFailure
  = DifferentArities
  | NotAllVars

-- | Compute a term that solves a flex-flex equation by intersection
--
-- @O(n^2)@
intersect
  :: forall a b
   . (Eq a, Eq b)
  => Seq (TmM a b)
  -> Seq (TmM a b)
  -> Either IntersectFailure (a -> TmM a b, a -> TmM a b)
intersect l m =
  -- use a church-encoded maybe for proper tail recursion
  Church.either Left Right $
  bimap (\f -> f . Var . M) (\f -> f . Var . M) <$> go l m
  where
    go
      :: forall c
       . Seq (Tm (Meta a b))
      -> Seq (Tm (Meta a b))
      -> Church.Either
           IntersectFailure
           (Tm c -> Tm c, Tm (Meta a b) -> Tm (Meta a b))
    go a b =
      case (Seq.viewl a, Seq.viewl b) of
        (EmptyL, EmptyL) -> Church.right (id, id)
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
        (_ :< xs, _ :< ys) -> Church.left NotAllVars *> go xs ys
        _ -> Church.left DifferentArities

ex3 :: (TmM String String, TmM String String)
ex3 = (res "alpha", res' "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y")]

ex4 :: (TmM String String, TmM String String)
ex4 = (res "alpha", res' "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex5 :: (TmM String String, TmM String String)
ex5 = (res "alpha", res' "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex6 :: (TmM String String, TmM String String)
ex6 = (res "alpha", res' "alpha")
  where
    Right (res, res') =
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

eta
  :: MonadSupply a m
  => TmM a b
  -> m (Maybe (Solution a b, TmM a b))
eta (Neutral (Var (M a)) xs) =
  case Seq.viewl xs of
    Fst :< _ -> do
      p <- Pair <$> fmap (Var . M) fresh <*> fmap (Var . M) fresh
      let sol = Solution a p
      pure $ Just (sol, Neutral p xs)
    Snd :< _ -> do
      p <- Pair <$> fmap (Var . M) fresh <*> fmap (Var . M) fresh
      let sol = Solution a p
      pure $ Just (sol, Neutral p xs)
    _ -> pure Nothing
eta _ = pure Nothing

zipMaybe :: [a] -> [b] -> Maybe [(a, b)]
zipMaybe a b = Church.maybe Nothing Just $ go a b
  where
    go [] [] = Church.just []
    go (_:_) [] = Church.nothing
    go [] (_:_) = Church.nothing
    go (x:xs) (y:ys) = ((x, y) :) <$> go xs ys

decompose
  :: (Eq a, Eq b, MonadSupply a m)
  => TmM a b
  -> TmM a b
  -> m (Result a b)
decompose (Neutral x xs) (Neutral y ys) =
  pure $
  case zipMaybe (toList xs) (toList ys) of
    Nothing -> Failure
    Just xys -> Success [] $ (x, y) : xys
decompose (Pair a a') (Pair b b') = pure $ Success [] [(a, b), (a', b')]
decompose Fst Fst = pure $ Success [] []
decompose Snd Snd = pure $ Success [] []
decompose (Lam s) (Lam s') = do
  v <- fresh
  pure $ Success [] [(instantiate1 (Var $ L v) s, instantiate1 (Var $ R v) s')]
decompose (Var a) (Var b) = pure $ if a == b then Success [] [] else Failure
decompose (Var (M _)) _ = pure Postpone
decompose _ (Var (M _)) = pure Postpone
decompose _ _ = pure Failure

data Result a b
  = Postpone
  | Failure
  | Success [Solution a b] [(TmM a b, TmM a b)]
  deriving (Eq, Show)

solve
  :: (Ord a, Ord b, MonadSupply a m)
  => TmM a b
  -> TmM a b
  -> m (Result a b)
solve tm1@(Neutral (Var (M a)) xs) tm2@(Neutral (Var (M b)) ys)
  | a == b =
    case intersect xs ys of
      Left DifferentArities -> pure Failure
      Left NotAllVars -> pure Postpone
      Right (sol, tm') -> do
        mv <- fresh
        pure $ Success [Solution a $ sol mv] [(tm' mv, tm' mv)]
  | Just keep <- varSet xs = do
      res <- prune keep tm2
      pure $ maybe Postpone (\(tm', sol) -> Success sol [(tm1, tm')]) res
  | otherwise = pure Postpone
solve tm1@(Neutral (Var (M a)) xs) y
  | occurs a y = pure Failure
  | Just vars <- distinctVarsContaining xs y =
      pure $
      Success [Solution a $ foldr lam y vars] []
  | Just keep <- varSet xs = do
      res <- prune keep y
      pure $ maybe Postpone (\(tm, sol) -> Success sol [(tm1, tm)]) res
  | otherwise = pure Postpone
solve x (Neutral (Var (M b)) ys) = solve (Neutral (Var (M b)) ys) x
solve a b = do
  ma <- eta a
  case ma of
    Nothing -> decompose a b
    Just (sol, a') -> pure $ Success [sol] [(a', b)]
