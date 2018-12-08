{-# language DeriveFunctor #-}
{-# language TemplateHaskell #-}
module Meta where

import Control.Lens.TH (makePrisms)
import Data.Bifunctor (Bifunctor(..))

data Meta m n = M m | N n
  deriving (Eq, Show)
makePrisms ''Meta

instance Bifunctor Meta where
  bimap f _ (M a) = M (f a)
  bimap _ f (N a) = N (f a)