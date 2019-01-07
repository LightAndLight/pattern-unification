{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language DeriveGeneric #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedLists #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Unify where

import Bound.Scope (instantiate1)
import Control.Lens.Getter ((^.))
import Control.Lens.Iso (iso)
import Control.Lens.Wrapped (Wrapped(..), Rewrapped, _Wrapped, _Unwrapped)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Data.Map (Map)

import qualified Data.Map as Map

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

data Twin a = Twin (Twinned Int Ty a) (Twinned Int Ty a)
  deriving Functor

data Equation a
  = Equation
  { eqCtx :: Map Int (Twin a)
  , eqLhsTm :: Twinned Int Tm a
  , eqLhsTy :: Twinned Int Ty a
  , eqRhsTm :: Twinned Int Tm a
  , eqRhsTy :: Twinned Int Ty a
  }

eta :: Equation a -> [Equation a]
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
