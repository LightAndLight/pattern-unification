{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Unify where

import Bound.Scope (instantiate1)
import Control.Lens.Getter ((^.))
import Control.Lens.Iso (iso)
import Control.Lens.Wrapped (Wrapped(..), Rewrapped, _Wrapped, _Unwrapped)
import Control.Monad.Except (MonadError, ExceptT(..), runExceptT, throwError)
import Control.Monad.Trans.Class (lift)
import Data.Map (Map)
import Data.Sequence (Seq, ViewL(..))

import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import Tm

data T a = L a | R a
newtype Twinned b f a = Twinned { unTwinned :: ExceptT (T b) f a }
  deriving (Functor, Applicative, Monad)

lt :: Applicative f => b -> f (Either (T b) a)
lt = pure . Left . L

rt :: Applicative f => b -> f (Either (T b) a)
rt = pure . Left . R

instance Wrapped (Twinned b f a) where
  type Unwrapped (Twinned b f a) = f (Either (T b) a)
  _Wrapped' = iso (runExceptT . unTwinned) (Twinned . ExceptT)
instance t ~ Twinned b' f' a' => Rewrapped (Twinned b f a) t where

data Twin b a = Twin (Twinned b Ty a) (Twinned b Ty a)
  deriving Functor

data Equation b a
  = Equation
  { eqCtx :: Map b (Twin b a)
  , eqLhsTm :: Twinned b Tm a
  , eqLhsTy :: Twinned b Ty a
  , eqRhsTm :: Twinned b Tm a
  , eqRhsTy :: Twinned b Ty a
  }

eta :: Equation Int a -> [Equation Int a]
eta (Equation ctx ltm lty rtm rty) =
  case (ltm ^. _Wrapped, lty ^. _Wrapped, rtm ^. _Wrapped, rty ^. _Wrapped) of
    (s, Pi a b, s', Pi a' b') ->
      [ Equation
          (Map.insert newVar (Twin (a ^. _Unwrapped) (a' ^. _Unwrapped)) ctx)
          ((s .@ lt newVar) ^. _Unwrapped)
          (instantiate1 (lt newVar) b ^. _Unwrapped)
          ((s' .@ rt newVar) ^. _Unwrapped)
          (instantiate1 (rt newVar) b' ^. _Unwrapped)
      ]
      where newVar = Map.size ctx
    (s, Sigma c d, s', Sigma c' d') ->
      [ Equation
          ctx
          ((s .@ Fst) ^. _Unwrapped)
          (c ^. _Unwrapped)
          ((s' .@ Fst) ^. _Unwrapped)
          (c' ^. _Unwrapped)
      , Equation
          ctx
          ((s .@ Snd) ^. _Unwrapped)
          (instantiate1 (s .@ Fst) d ^. _Unwrapped)
          ((s' .@ Snd) ^. _Unwrapped)
          (instantiate1 (s' .@ Fst) d' ^. _Unwrapped)
      ]
    _ -> []

data UnifyError b a
  = Mismatch (Twinned b Tm a) (Twinned b Tm a)
  | NotInScope (Either b a)

lookupTwin
  :: (MonadError (UnifyError b a) m, Ord b)
  => T b
  -> Map b (Twin b a)
  -> m (Twinned b Tm a)
lookupTwin (L b) mp =
  case Map.lookup b mp of
    Just (Twin a _) -> pure a
    Nothing -> throwError $ NotInScope (Left b)
lookupTwin (R b) mp =
  case Map.lookup b mp of
    Just (Twin _ a) -> pure a
    Nothing -> throwError $ NotInScope (Left b)

decompose
  :: forall m a b
   . (MonadError (UnifyError b a) m, Eq a, Ord b)
  => (a -> m (Twinned b Tm a))
  -> Map b (Twin b a)
  -> (Tm (Either (T b) a), Seq (Tm (Either (T b) a)))
  -> (Tm (Either (T b) a), Seq (Tm (Either (T b) a)))
  -> m (Maybe [Equation b a])
decompose globals ctx (Var x, xs) (Var y, ys) = do
  xTy <- either (flip lookupTwin ctx) globals x
  yTy <- either (flip lookupTwin ctx) globals y
  Just <$> go (Var x) (xTy ^. _Wrapped) xs (Var y) (yTy ^. _Wrapped) ys
  where
    go
      :: Tm (Either (T b) a)
      -> Ty (Either (T b) a)
      -> Seq (Tm (Either (T b) a))

      -> Tm (Either (T b) a)
      -> Ty (Either (T b) a)
      -> Seq (Tm (Either (T b) a))

      -> m [Equation b a]
    go va tas as vb tbs bs =
      case (tas, Seq.viewl as, tbs, Seq.viewl bs) of
        (_, EmptyL, _, EmptyL) ->
          pure $
          [ Equation
              ctx
              (va ^. _Unwrapped)
              (tas ^. _Unwrapped)
              (vb ^. _Unwrapped)
              (tbs ^. _Unwrapped)
          ]
        (Sigma s _, Fst :< aas, Sigma s' _, Fst :< bbs) ->
          go
            (va .@ Fst) s aas
            (vb .@ Fst) s' bbs
        (Sigma _ t, Snd :< aas, Sigma _ t', Snd :< bbs) ->
          go
            (va .@ Snd) (instantiate1 (va .@ Fst) t) aas
            (vb .@ Snd) (instantiate1 (vb .@ Fst) t') bbs
        (Pi s t, aa :< aas, Pi s' t', bb :< bbs) ->
          (Equation
            ctx
            (aa ^. _Unwrapped)
            (s ^. _Unwrapped)
            (bb ^. _Unwrapped)
            (s' ^. _Unwrapped) :) <$>
          go
            (va .@ aa) (instantiate1 aa t) aas
            (vb .@ bb) (instantiate1 bb t') bbs
        _ ->
          throwError $
          Mismatch
            (App (Var x) xs ^. _Unwrapped)
            (App (Var y) ys ^. _Unwrapped)
decompose _ _ _ _ = pure Nothing

varsMatch :: (Eq b, Eq a) => Either (T b) a -> Either (T b) a -> Bool
varsMatch (Left (L a)) (Left (L b)) = a == b
varsMatch (Left (L a)) (Left (R b)) = a == b
varsMatch (Left (R a)) (Left (L b)) = a == b
varsMatch (Left (R a)) (Left (R b)) = a == b
varsMatch (Right a) (Right b) = a == b
varsMatch _ _ = False

rigidRigid
  :: (MonadError (UnifyError b a) m, Eq a, Ord b)
  => (a -> m (Twinned b Tm a))
  -> Equation b a
  -> m [Equation b a]
rigidRigid globals (Equation ctx ltm lty rtm rty) =
  case (ltm ^. _Wrapped, lty ^. _Wrapped, rtm ^. _Wrapped, rty ^. _Wrapped) of
    (Pi a b, Type, Pi a' b', Type) ->
      pure
      [ Equation
          ctx
          (a ^. _Unwrapped)
          (Type ^. _Unwrapped)
          (a' ^. _Unwrapped)
          (Type ^. _Unwrapped)
      , Equation
          ctx
          (Lam b ^. _Unwrapped)
          (Pi Type (lift Type) ^. _Unwrapped)
          (Lam b' ^. _Unwrapped)
          (Pi Type (lift Type) ^. _Unwrapped)
      ]
    (Sigma a b, Type, Sigma a' b', Type) ->
      pure
      [ Equation
          ctx
          (a ^. _Unwrapped)
          (Type ^. _Unwrapped)
          (a' ^. _Unwrapped)
          (Type ^. _Unwrapped)
      , Equation
          ctx
          (Lam b ^. _Unwrapped)
          (Pi Type (lift Type) ^. _Unwrapped)
          (Lam b' ^. _Unwrapped)
          (Pi Type (lift Type) ^. _Unwrapped)
      ]
    (App x xs, t, App y ys, t') -> do
      meqs <- decompose globals ctx (x, xs) (y, ys)
      case meqs of
        Nothing -> throwError $ Mismatch ltm rtm
        Just eqs ->
          pure $
          Equation
            ctx
            (t ^. _Unwrapped)
            (Type ^. _Unwrapped)
            (t' ^. _Unwrapped)
            (Type ^. _Unwrapped) :
          eqs
    (Var a, t, Var b, t') | varsMatch a b ->
        pure
        [ Equation
            ctx
            (t ^. _Unwrapped)
            (Type ^. _Unwrapped)
            (t' ^. _Unwrapped)
            (Type ^. _Unwrapped)
        ]
    -- woo
    (Type, Type, Type, Type) -> pure []
    _ -> throwError $ Mismatch ltm rtm
