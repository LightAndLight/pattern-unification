{-# language DefaultSignatures #-}
{-# language FlexibleInstances, UndecidableInstances #-}
{-# language FunctionalDependencies, MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Solver.Class where

import Control.Lens.TH (makeLenses, makePrisms, makeClassyPrisms)
import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Writer (WriterT)

import Equation
import LambdaPi

data Meta a = M a | N (Head a)
  deriving (Eq, Show)
makePrisms ''Meta

instance AsHead (Meta a) a where; _Head = _N

data Problem a
  = Problem
  { _problemSig :: [(a, Tm (Meta a))]
  , _problemEquation :: Equation Meta a
  }
  deriving (Eq, Show)
makeLenses ''Problem

data MetaEntry a
  = MetaDecl a (Tm (Meta a))
  | MetaProblem (Problem a)
  deriving (Eq, Show)
makePrisms ''MetaEntry

data SolverError a
  = MetaNotFound (Meta a)
  | Occurs (Meta a) (Tm (Meta a))
  | DisagreeingSolutions a (Tm (Meta a)) (Tm (Meta a))
  deriving (Eq, Show)

class Monad m => MonadSolver a m | m -> a where
  -- | View the current problem we're working on
  currentProblem :: m (Maybe (Problem a))

  -- | Provide a solution for a metavariable
  solve :: a -> Tm (Meta a) -> m ()

  -- | Remove the current problem and return its signature to the context
  dissolve :: m ()

  -- | Add the entry to the left to current problem's signature
  expandSig :: m ()

  -- | View the entry to the left of the current problem
  lookLeft :: m (Maybe (MetaEntry a))

  -- | Swap the current problem with the entry on its left
  swapLeft :: m ()

  default currentProblem :: (MonadSolver a u, MonadTrans t, t u ~ m) => m (Maybe (Problem a))
  currentProblem = lift currentProblem

  default solve :: (MonadSolver a u, MonadTrans t, t u ~ m) => a -> Tm (Meta a) -> m ()
  solve a b = lift $ solve a b

  default dissolve :: (MonadSolver a u, MonadTrans t, t u ~ m) => m ()
  dissolve = lift dissolve

  default expandSig :: (MonadSolver a u, MonadTrans t, t u ~ m) => m ()
  expandSig = lift expandSig

  default lookLeft :: (MonadSolver a u, MonadTrans t, t u ~ m) => m (Maybe (MetaEntry a))
  lookLeft = lift lookLeft

  default swapLeft :: (MonadSolver a u, MonadTrans t, t u ~ m) => m ()
  swapLeft = lift swapLeft

instance MonadSolver a m => MonadSolver a (ExceptT e m)
instance MonadSolver a m => MonadSolver a (ReaderT r m)
instance MonadSolver a m => MonadSolver a (StateT s m)
instance (MonadSolver a m, Monoid w) => MonadSolver a (WriterT w m)

makeClassyPrisms ''SolverError
