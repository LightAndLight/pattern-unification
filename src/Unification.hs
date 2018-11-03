{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope
  ( instantiate
  , mapBound
  )
import Control.Lens.Fold ((^?))
import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)
import Data.Sequence (Seq, ViewL(..))

import qualified Bound.Scope as Bound
import qualified Data.Sequence as Seq

import LambdaPi
import Supply.Class

data CtxEntry a
  = Twin (Tm a) (Tm a)
  | Only (Tm a)
  deriving (Eq, Show)

data UnifyError a
  = Mismatch
  { errLhsTm :: Tm (Head a)
  , errLhsTy :: Tm (Head a)
  , errRhsTm :: Tm (Head a)
  , errRhsTy :: Tm (Head a)
  }
  | NotFound a
  | ExpectedTwin a
  | ExpectedOnly a
  deriving (Eq, Show)

getTwin
  :: (MonadError (UnifyError a) m, Eq a)
  => [(a, CtxEntry b)]
  -> a
  -> m (Tm b, Tm b)
getTwin ctx a = do
  a' <- maybe (throwError $ NotFound a) pure $ lookup a ctx
  case a' of
    Twin x y -> pure (x, y)
    _ -> throwError $ ExpectedTwin a

getOnly
  :: (MonadError (UnifyError a) m, Eq a)
  => [(a, CtxEntry b)]
  -> a
  -> m (Tm b)
getOnly ctx a = do
  a' <- maybe (throwError $ NotFound a) pure $ lookup a ctx
  case a' of
    Only x -> pure x
    _ -> throwError $ ExpectedOnly a

data Equation a
  = Equation
  { eqCtx :: [(a, CtxEntry (Head a))]
  , lhsTm :: Tm (Head a)
  , lhsTy :: Tm (Head a)
  , rhsTm :: Tm (Head a)
  , rhsTy :: Tm (Head a)
  }
  deriving (Eq, Show)

eta
  :: ( Eq a, Show a
     , MonadSupply a m
     , MonadError (UnifyError a) m
     )
  => Equation a -> m [Equation a]
eta (Equation ctx a (Pi 1 b c) a' (Pi 1 b' c')) = do
  x <- fresh
  pure
    [ Equation ((x, Twin b b') : ctx)
        (apply (Var $ VL x) a ) (apply (Var $ VL x) (Lam 1 $ teleScope c ))
        (apply (Var $ VR x) a') (apply (Var $ VR x) (Lam 1 $ teleScope c'))
    ]
eta (Equation _ _ Pi{} _ Pi{}) = error "TODO: telescoped pi types"
eta (Equation ctx a (Sigma b c) a' (Sigma b' c')) =
  pure
  [ Equation ctx
      aFst b
      aFst b'
  , Equation ctx
      (Neutral a  [Snd]) (Bound.instantiate1 aFst  c )
      (Neutral a' [Snd]) (Bound.instantiate1 a'Fst c')
  ]
  where
    aFst = Neutral a [Fst]
    a'Fst = Neutral a' [Fst]
-- TODO can this system solve universe constraints?
eta (Equation _ Type Type Type Type) = pure []
eta (Equation ctx (Pi 1 a b) Type (Pi 1 a' b') Type) =
  pure
  [ Equation ctx
      a  Type
      a' Type
  , Equation ctx
      (Lam 1 $ teleScope b ) (Pi 1 a  $ liftTele Type)
      (Lam 1 $ teleScope b') (Pi 1 a' $ liftTele Type)
  ]
eta (Equation _ Pi{} Type Pi{} Type) =
  error "TODO: telescoped pi types"
eta (Equation ctx (Sigma a b) Type (Sigma a' b') Type) =
  pure
  [ Equation ctx
      a  Type
      a' Type
  , Equation ctx
      (Lam 1 $ mapBound (const 0) b ) (Pi 1 a  $ liftTele Type)
      (Lam 1 $ mapBound (const 0) b') (Pi 1 a' $ liftTele Type)
  ]
eta (Equation ctx tm1@(Neutral (Var (V a)) _) _ tm2@(Neutral (Var (V a')) _) _) = do
  aTy <- getOnly ctx a
  a'Ty <- getOnly ctx a'
  unless (a == a') .
    throwError $ Mismatch (Var $ V a) aTy (Var $ V a') a'Ty
  (Equation ctx aTy Type a'Ty Type :) <$>
    matchSpines ctx (aTy, tm1) (a'Ty, tm2)
eta (Equation ctx tm1@(Neutral (Var (VL a)) _) _ tm2@(Neutral (Var (VL a')) _) _) = do
  (aTyL, _) <- getTwin ctx a
  (_, a'TyR) <- getTwin ctx a'
  unless (a == a') .
    throwError $ Mismatch (Var $ VL a) aTyL (Var $ VR a') a'TyR
  (Equation ctx aTyL Type a'TyR Type :) <$>
    matchSpines ctx (aTyL, tm1) (a'TyR, tm2)
eta (Equation _ a b a' b') = throwError $ Mismatch a b a' b'

matchSpines
  :: forall a m
   . (Show a, MonadError (UnifyError a) m)
  => [(a, CtxEntry (Head a))]
  -> (Tm (Head a), Tm (Head a))
  -> (Tm (Head a), Tm (Head a))
  -> m [Equation a]
matchSpines ctx (headTy, a1) (headTy', a2) = do
  (hd, as) <-
    maybe
      (error $ show a1 <> " is not a neutral term")
      pure
      (a1 ^? _Neutral)
  (hd', as') <-
    maybe
      (error $ show a2 <> " is not a neutral term")
      pure
      (a2 ^? _Neutral)
  go (headTy, Var hd, as) (headTy', Var hd', as')
  where
    go
      :: (Show a, MonadError (UnifyError a) m)
      => (Tm (Head a), Tm (Head a), Seq (Elim Tm (Head a)))
      -> (Tm (Head a), Tm (Head a), Seq (Elim Tm (Head a)))
      -> m [Equation a]
    go (ty, hd, as) (ty', hd', as') =
      case (Seq.viewl as, Seq.viewl as') of
        (EmptyL, EmptyL) -> pure []
        (x :< xs, y :< ys) ->
          case (ty, ty') of
            (Pi 1 a b, Pi 1 a' b') ->
              case (x, y) of
                (Elim_Tm c, Elim_Tm c') ->
                  (Equation ctx c a c' a' :) <$>
                  go
                    (instantiate (const c)  $ teleScope b , apply c  hd , xs)
                    (instantiate (const c') $ teleScope b', apply c' hd', ys)
                _ ->
                  error $
                  "spines don't match:\n\n" <>
                  show x <>
                  "\n\nand\n\n" <>
                  show y
            (Pi{}, Pi{}) -> error "TODO: telescoped pi types"
            (Sigma a b, Sigma a' b') ->
              case (x, y) of
                (Elim_Fst, Elim_Fst) ->
                  go
                    (a , elim hd  Elim_Fst, xs)
                    (a', elim hd' Elim_Fst, ys)
                (Elim_Snd, Elim_Snd) ->
                  go
                    ( Bound.instantiate1 (apply Fst hd ) b
                    , elim hd Elim_Snd
                    , xs
                    )
                    ( Bound.instantiate1 (apply Fst hd') b'
                    , elim hd' Elim_Snd
                    , ys
                    )
                _ ->
                  error $
                  "spines don't match:\n\n" <>
                  show x <>
                  "\n\nand\n\n" <>
                  show y
            _ ->
              error $
              "head types are not eliminatable:\n\n" <>
              show ty <>
              "\n\nand\n\n" <>
              show ty'
        -- failure cases? the paper says the spines must be the same length
        (_ :< _, EmptyL) ->
          error $
          "spines are different lengths:\n\n" <>
          show as <>
          "\n\nand\n\n" <> show as'
        (EmptyL, _ :< _) ->
          error $
          "spines are different lengths:\n\n" <>
          show as <>
          "\n\nand\n\n" <>
          show as'
