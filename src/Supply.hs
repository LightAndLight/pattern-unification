{-# language GeneralizedNewtypeDeriving #-}
{-# language FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Supply where


import Control.Monad.Except (MonadError(..))
import Control.Monad.Reader (MonadReader(..), ReaderT, runReaderT)
import Control.Monad.State (MonadState(..), StateT, evalStateT)
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.Trans.Class (MonadTrans(..))

import Supply.Class

newtype SupplyT s v m a
  = SupplyT
  { unSupplyT :: ReaderT (s -> (v, s)) (StateT s m) a
  } deriving (Functor, Applicative, Monad)

instance MonadTrans (SupplyT s v) where
  lift = SupplyT . lift . lift

instance Monad m => MonadSupply v (SupplyT s v m) where
  fresh = SupplyT $ ask >>= state

runSupplyT
  :: Monad m
  => s -- ^ Seed
  -> (s -> (v, s)) -- ^ Generator
  -> SupplyT s v m a
  -> m a
runSupplyT s g = flip evalStateT s . flip runReaderT g . unSupplyT

instance MonadState s m => MonadState s (SupplyT a b m) where
  state = SupplyT . lift . lift . state

instance MonadReader r m => MonadReader r (SupplyT a b m) where
  ask = SupplyT . lift $ lift ask
  local f m =
    SupplyT $ do
      a <- get; b <- ask
      lift $ lift $ local f (runSupplyT a b m)

instance MonadWriter w m => MonadWriter w (SupplyT a b m) where
  writer = SupplyT . lift . lift . writer
  listen m =
    SupplyT $ do
      a <- get; b <- ask
      lift $ lift $ listen (runSupplyT a b m)
  pass m =
    SupplyT $ do
      a <- get; b <- ask
      lift $ lift $ pass (runSupplyT a b m)

instance MonadError e m => MonadError e (SupplyT a b m) where
  throwError = SupplyT . lift . lift . throwError
  catchError m f =
    SupplyT $ do
      a <- get; b <- ask
      lift $ lift $ catchError (runSupplyT a b m) (runSupplyT a b . f)
