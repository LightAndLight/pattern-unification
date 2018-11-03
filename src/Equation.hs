module Equation where

import LambdaPi

data CtxEntry a
  = Twin (Tm a) (Tm a)
  | Only (Tm a)
  deriving (Eq, Show)

data Equation a
  = Equation
  { eqCtx :: [(a, CtxEntry (Head a))]
  , lhsTm :: Tm (Head a)
  , lhsTy :: Tm (Head a)
  , rhsTm :: Tm (Head a)
  , rhsTy :: Tm (Head a)
  }
  deriving (Eq, Show)