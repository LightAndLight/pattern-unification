{-# language FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
module Supply where

import Control.Monad.Except (MonadError(..))
import Control.Monad.Reader (MonadReader(..), ReaderT, runReaderT)
import Control.Monad.State (MonadState(..), StateT, evalStateT)
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Functor.Identity (Identity(..))

import Supply.Class

newtype SupplyT s v m a
  = SupplyT
  { unSupplyT :: ReaderT (s -> (v, s)) (StateT s m) a
  } deriving (Functor, Applicative, Monad)

type Supply s v a = SupplyT s v Identity a

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

runSupply
  :: s -- ^ Seed
  -> (s -> (v, s)) -- ^ Generator
  -> Supply s v a
  -> a
runSupply s g = runIdentity . runSupplyT s g

instance MonadState s m => MonadState s (SupplyT a b m) where
  state = SupplyT . lift . lift . state

instance MonadReader r m => MonadReader r (SupplyT a b m) where
  ask = SupplyT . lift $ lift ask
  local f m =
    SupplyT $ do
      a <- get; b <- ask
      lift $ lift $ local f (runSupplyT a b m)

instance MonadWriter w m => MonadWriter w (SupplyT a b m) where
  writer = SupplyT . writer
  listen = SupplyT . listen . unSupplyT
  pass = SupplyT . pass . unSupplyT

instance MonadError e m => MonadError e (SupplyT a b m) where
  throwError = SupplyT . throwError
  catchError m f = SupplyT $ catchError (unSupplyT m) (unSupplyT . f)
