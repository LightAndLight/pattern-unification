{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language TemplateHaskell #-}
module Unify where

import Bound.Scope (Scope)

import Tm

data Equation a
  = Equation
  { eqLhsTm :: Tm a
  , eqLhsTy :: Ty a
  , eqRhsTm :: Tm a
  , eqRhsTy :: Ty a
  }
  deriving (Functor, Foldable, Traversable)

data Problem a
  = Done (Equation a)
  | More (Ty a) (Ty a) (Scope () Problem a)
  deriving (Functor, Foldable, Traversable)

eta :: Problem a -> Maybe (Problem a)
eta (Equation ltm lty rtm rty) = _
