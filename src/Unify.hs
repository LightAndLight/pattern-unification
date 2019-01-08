{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language DeriveGeneric #-}
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
import Control.Monad.Except (ExceptT(..), runExceptT)
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
          (App s [lt newVar] ^. _Unwrapped)
          (instantiate1 (lt newVar) b ^. _Unwrapped)
          (App s' [rt newVar] ^. _Unwrapped)
          (instantiate1 (rt newVar) b' ^. _Unwrapped)
      ]
      where newVar = Map.size ctx
    (s, Sigma c d, s', Sigma c' d') ->
      [ Equation
          ctx
          (App s [Fst] ^. _Unwrapped)
          (c ^. _Unwrapped)
          (App s' [Fst] ^. _Unwrapped)
          (c' ^. _Unwrapped)
      , Equation
          ctx
          (App s [Snd] ^. _Unwrapped)
          (instantiate1 (App s [Fst]) d ^. _Unwrapped)
          (App s' [Snd] ^. _Unwrapped)
          (instantiate1 (App s' [Fst]) d' ^. _Unwrapped)
      ]
    _ -> []

lookupTwin :: Ord b => T b -> Map b (Twin b a) -> Maybe (Twinned b Tm a)
lookupTwin (L b) mp =
  case Map.lookup b mp of
    Just (Twin a _) -> Just a
    Nothing -> Nothing
lookupTwin (R b) mp =
  case Map.lookup b mp of
    Just (Twin _ a) -> Just a
    Nothing -> Nothing

decompose
  :: forall a b
   . (Eq a, Ord b)
  => (a -> Maybe (Twinned b Tm a))
  -> Map b (Twin b a)
  -> (Tm (Either (T b) a), Seq (Tm (Either (T b) a)))
  -> (Tm (Either (T b) a), Seq (Tm (Either (T b) a)))
  -> [Equation b a]
decompose globals ctx (Var x, xs) (Var y, ys) =
  case (,) <$> xTy <*> yTy of
    Just (t1, t2) ->
      go (Var x) (t1 ^. _Wrapped) xs (Var y) (t2 ^. _Wrapped) ys
    _ -> []
  where
    xTy = either (flip lookupTwin ctx) globals x
    yTy = either (flip lookupTwin ctx) globals y

    go
      :: Tm (Either (T b) a)
      -> Ty (Either (T b) a)
      -> Seq (Tm (Either (T b) a))

      -> Tm (Either (T b) a)
      -> Ty (Either (T b) a)
      -> Seq (Tm (Either (T b) a))

      -> [Equation b a]
    go va tas as vb tbs bs =
      case (tas, Seq.viewl as, tbs, Seq.viewl bs) of
        (_, EmptyL, _, EmptyL) ->
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
          Equation
            ctx
            (aa ^. _Unwrapped)
            (s ^. _Unwrapped)
            (bb ^. _Unwrapped)
            (s' ^. _Unwrapped) :
          go
            (va .@ aa) (instantiate1 aa t) aas
            (vb .@ bb) (instantiate1 bb t') bbs
        _ -> []
decompose _ _ _ _ = []

rigidRigid :: (Eq a, Ord b) => (a -> Maybe (Twinned b Tm a)) -> Equation b a -> [Equation b a]
rigidRigid globals (Equation ctx ltm lty rtm rty) =
  case (ltm ^. _Wrapped, lty ^. _Wrapped, rtm ^. _Wrapped, rty ^. _Wrapped) of
    (Pi a b, Type, Pi a' b', Type) ->
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
    (App x xs, t, App y ys, t') ->
      Equation
        ctx
        (t ^. _Unwrapped)
        (Type ^. _Unwrapped)
        (t' ^. _Unwrapped)
        (Type ^. _Unwrapped) :
      decompose globals ctx (x, xs) (y, ys)
