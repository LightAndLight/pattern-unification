{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language QuantifiedConstraints #-}
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
import Data.Functor.Identity (Identity(..))
import Data.Monoid (Ap(..))
import Data.Set (Set)
import Data.Sequence (Seq, ViewL(..))
import Data.STRef (STRef)
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

type TmM f a b = Tm (Meta f a b)

data Solution f a b = Solution (f a) (TmM f a b)
deriving instance
  (forall x. Eq x => Eq (f x), Eq a, Eq b) => Eq (Solution f a b)
deriving instance
  (forall x. Show x => Show (f x), Show a, Show b) => Show (Solution f a b)

prettySolution
  :: (forall x. (x -> Doc) -> f x -> Doc)
  -> (a -> Doc)
  -> (b -> Doc)
  -> Solution f a b
  -> Doc
prettySolution fDoc aDoc bDoc (Solution a b) =
  Print.hsep
    [ Print.char '?' <> fDoc aDoc a
    , Print.text ":="
    , prettyTm (prettyMeta fDoc aDoc bDoc) b
    ]

instance
  ( forall x. Pretty x => Pretty (f x)
  , Pretty a
  , Pretty b
  ) => Pretty (Solution f a b) where

  pretty (Solution a b) =
    Print.hsep
      [ Print.char '?' <> pretty a
      , Print.text ":="
      , pretty b
      ]

occurs
  :: forall a b f
   . (forall x. Eq x => Eq (f x), Eq a, Eq b)
  => f a
  -> TmM f a b
  -> Bool
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

    go :: forall c. (Eq a, Eq c) => Bool -> Bool -> TmM f a c -> Bool
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
  :: forall t a b f
   . ( Traversable t
     , forall x. Eq x => Eq (f x)
     , forall x. Ord x => Ord (f x)
     , Ord a
     , Ord b
     )
  => t (TmM f a b)
  -> TmM f a b
  -> Maybe [Meta f a b]
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
      :: (MonadState (Set (Meta f a b)) m, Ord b)
      => TmM f a b
      -> m (Maybe (DList (Meta f a b)))
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
  :: forall a b f
   . (Eq a, Eq b)
  => Seq (TmM f a b)
  -> Seq (TmM f a b)
  -> Either IntersectFailure (f a -> TmM f a b, f a -> TmM f a b)
intersect l m =
  -- use a church-encoded maybe for proper tail recursion
  Church.either Left Right $
  bimap (\f -> f . Var . M) (\f -> f . Var . M) <$> go l m
  where
    go
      :: forall c
       . Seq (TmM f a b)
      -> Seq (TmM f a b)
      -> Church.Either
           IntersectFailure
           (Tm c -> Tm c, TmM f a b -> TmM f a b)
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

ex3 :: (TmM Identity String String, TmM Identity String String)
ex3 = (res $ Identity "alpha", res' $ Identity "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y")]

ex4 :: (TmM Identity String String, TmM Identity String String)
ex4 = (res $ Identity "alpha", res' $ Identity "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "x"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex5 :: (TmM Identity String String, TmM Identity String String)
ex5 = (res $ Identity "alpha", res' $ Identity "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "x"), Var (N "y"), Var (N "z")]

ex6 :: (TmM Identity String String, TmM Identity String String)
ex6 = (res $ Identity "alpha", res' $ Identity "alpha")
  where
    Right (res, res') =
      intersect
        [Var (N "x"), Var (N "y"), Var (N "x")]
        [Var (N "y"), Var (N "y"), Var (N "z")]

pruneArgs
  :: forall a b f
    . (b -> Maybe b)
  -> Seq (TmM f a b)
  -> Maybe (f a -> TmM f a Void, f a -> TmM f a b)
pruneArgs ctx =
  Church.maybe Nothing Just .
  fmap (bimap (. (Var . M)) (. (Var . M))) .
  go
  where
    go
      :: forall c
       . Seq (TmM f a b)
      -> Church.Maybe (Tm c -> Tm c, TmM f a b -> TmM f a b)
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
  :: forall a b m f
   . (Ord b, MonadSupply (f a) m)
  => Set b
  -> TmM f a b
  -> m (Maybe (TmM f a b, [Solution f a b]))
prune keep =
  runMaybeT .
  runWriterT .
  go False (\x -> x <$ guard (Set.member x keep))
  where
    go
      :: forall c
       . Bool
      -> (c -> Maybe c)
      -> TmM f a c
      -> WriterT [Solution f a b] (MaybeT m) (TmM f a c)
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

varSet :: Ord b => Seq (TmM f a b) -> Maybe (Set b)
varSet = Church.maybe Nothing Just . go
  where
    go x =
      case Seq.viewl x of
        EmptyL -> Church.just mempty
        Var (N a) :< xs -> Set.insert a <$> go xs
        _ -> Church.nothing

eta
  :: MonadSupply (f a) m
  => TmM f a b
  -> m (Maybe (Solution f a b, TmM f a b))
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
  :: (forall x. Eq x => Eq (f x), Eq a, Eq b, MonadSupply (f a) m)
  => TmM f a b
  -> TmM f a b
  -> m (Result f a b)
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
  pure $
    Success [] [(instantiate1 (Var $ L v) s, instantiate1 (Var $ R v) s')]
decompose (Var a) (Var b) = pure $ if a == b then Success [] [] else Failure
decompose (Var (M _)) _ = pure Postpone
decompose _ (Var (M _)) = pure Postpone
decompose _ _ = pure Failure

data Result f a b
  = Postpone
  | Failure
  | Success [Solution f a b] [(TmM f a b, TmM f a b)]
deriving instance
  (forall x. Eq x => Eq (f x), Eq a, Eq b) => Eq (Result f a b)
deriving instance
  (forall x. Show x => Show (f x), Show a, Show b) => Show (Result f a b)

solve1
  :: ( forall x. Eq x => Eq (f x)
     , forall x. Ord x => Ord (f x)
     , Ord a
     , Ord b
     , MonadSupply (f a) m
     )
  => TmM f a b
  -> TmM f a b
  -> m (Result f a b)
solve1 tm1@(Neutral (Var (M a)) xs) tm2@(Neutral (Var (M b)) ys)
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
solve1 tm1@(Neutral (Var (M a)) xs) y
  | occurs a y = pure Failure
  | Just vars <- distinctVarsContaining xs y =
      pure $
      Success [Solution a $ foldr lam y vars] []
  | Just keep <- varSet xs = do
      res <- prune keep y
      pure $ maybe Postpone (\(tm, sol) -> Success sol [(tm1, tm)]) res
  | otherwise = pure Postpone
solve1 x (Neutral (Var (M b)) ys) = solve1 (Neutral (Var (M b)) ys) x
solve1 a b = do
  ma <- eta a
  case ma of
    Nothing -> decompose a b
    Just (sol, a') -> pure $ Success [sol] [(a', b)]
