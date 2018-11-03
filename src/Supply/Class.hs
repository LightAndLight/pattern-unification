{-# language DefaultSignatures #-}
{-# language FlexibleInstances, UndecidableInstances #-}
{-# language FunctionalDependencies, MultiParamTypeClasses #-}
{-# language TypeFamilies #-}
module Supply.Class where

import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Writer (WriterT)

class Monad m => MonadSupply a m | m -> a where
  fresh :: m a

  default fresh :: (MonadSupply a u, MonadTrans t, t u ~ m) => m a
  fresh = lift fresh

instance MonadSupply a m => MonadSupply a (ExceptT e m)
instance MonadSupply a m => MonadSupply a (ReaderT r m)
instance MonadSupply a m => MonadSupply a (StateT s m)
instance (MonadSupply a m, Monoid w) => MonadSupply a (WriterT w m)
