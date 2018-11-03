{-# language FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language TemplateHaskell #-}
module Solver where

import Control.Lens.Cons (_head)
import Control.Lens.Fold (preuse)
import Control.Lens.Getter (use)
import Control.Lens.Prism (_Just)
import Control.Lens.Review ((#))
import Control.Lens.Setter ((%=), (.=), (<>=))
import Control.Lens.TH (makeLenses)
import Control.Monad (unless)
import Control.Monad.Except (MonadError(..), ExceptT(..), runExceptT)
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.State (MonadState(..), StateT, evalStateT)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Writer (MonadWriter(..))
import Data.Maybe (fromMaybe)

import LambdaPi
import Solver.Class

data MetaContext a
  = MetaContext
  { _mcEntriesLeft :: [MetaEntry a]
  , _mcCurrentProblem :: Maybe (Problem a)
  , _mcEntriesRight :: [MetaEntry a]
  , _mcSolutions :: [(a, Tm (Meta a))]
  } deriving (Eq, Show)
makeLenses ''MetaContext

newtype SolverT v e m a
  = SolverT
  { unSolverT :: StateT (MetaContext v) (ExceptT e m) a
  } deriving (Functor, Applicative, Monad, MonadError e)

runSolverT :: Monad m => MetaContext v -> SolverT v e m a -> m (Either e a)
runSolverT c = runExceptT . flip evalStateT c . unSolverT

instance (Eq a, AsSolverError e a, Monad m) => MonadSolver a e (SolverT a e m) where
  currentProblem =
    SolverT $ use mcCurrentProblem

  solve a tm =
    SolverT $ do
      solutions <- use mcSolutions
      let
        tm' =
          tm >>=
          \case
            M b -> fromMaybe (pure $ M b) (lookup b solutions)
            N b -> pure $ N b
      case lookup a solutions of
        Nothing -> mcSolutions %= ((a, tm') :)
        Just tm'' ->
          unless (tm' == tm'') . throwError $
          _DisagreeingSolutions # (a, tm', tm'')

  dissolve = do
    p <- currentProblem
    case p of
      Nothing -> pure ()
      Just (Problem sig _) ->
        SolverT $ do
          mcEntriesLeft <>= fmap (uncurry MetaDecl) sig
          mcCurrentProblem .= Nothing

  expandSig =
    SolverT $ do
      l <- use mcEntriesLeft
      case l of
        MetaDecl a b : xs -> do
          mcEntriesLeft .= xs
          mcCurrentProblem._Just.problemSig %= ((a, b) :)
        _ -> pure ()

  lookLeft = SolverT $ preuse (mcEntriesLeft._head)

  swapLeft =
    SolverT $ do
      l <- use mcEntriesLeft
      case l of
        [] -> pure ()
        x:xs -> do
          mcEntriesLeft .= xs
          mcEntriesRight %= (x :)

instance MonadTrans (SolverT v e) where
  lift = SolverT . lift . lift

instance MonadState s m => MonadState s (SolverT a b m) where
  state = SolverT . lift . lift . state

instance MonadReader r m => MonadReader r (SolverT a b m) where
  ask = SolverT ask
  local f = SolverT . local f . unSolverT

instance MonadWriter w m => MonadWriter w (SolverT a b m) where
  writer = SolverT . lift . lift . writer
  listen = SolverT . listen . unSolverT
  pass = SolverT . pass . unSolverT

instance MonadError e m => MonadError e (SolverT a b m) where
  throwError = SolverT . lift . lift . throwError
  catchError m f =
    SolverT $ do
      a <- get
      lift $ ExceptT $ catchError (runSolverT a m) (runSolverT a . f)
