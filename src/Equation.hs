{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Equation where

import LambdaPi

data CtxEntry a
  = Twin (Tm a) (Tm a)
  | Only (Tm a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Equation f a
  = Equation
  { eqCtx :: [(a, CtxEntry (f a))]
  , lhsTm :: Tm (f a)
  , lhsTy :: Tm (f a)
  , rhsTm :: Tm (f a)
  , rhsTy :: Tm (f a)
  }
  deriving (Eq, Show)