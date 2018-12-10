{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Constraint where

import LambdaPi
import Meta

data Constraint meta var
  = Equals
  { eqLhs :: Tm (Meta meta var)
  , eqRhs :: Tm (Meta meta var)
  }
  | HasType
  { eqCtx :: [(var, Tm (Meta meta var))]
  , eqTm :: Tm (Meta meta var)
  , eqTy :: Tm (Meta meta var)
  }
