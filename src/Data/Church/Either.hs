{-# language RankNTypes #-}
{-# language NoImplicitPrelude #-}
module Data.Church.Either where

import Control.Applicative (Applicative(..))
import Control.Monad (Monad(..))
import Data.Function ((.))
import Data.Functor (Functor(..))

newtype Either a b
  = Either { unEither :: forall r. (a -> r) -> (b -> r) -> r }

either :: (a -> r) -> (b -> r) -> Either a b -> r
either l r (Either e) = e l r

left :: a -> Either a b
left a = Either (\l _ -> l a)

right :: b -> Either a b
right b = Either (\_ r -> r b)

instance Functor (Either a) where
  fmap f (Either e) = Either (\l r -> e l (r . f))

instance Applicative (Either a) where
  pure = right
  Either mf <*> Either ma = Either (\l r -> mf l (\f -> ma l (\a -> r (f a))))

instance Monad (Either a) where
  Either ma >>= f = Either (\l r -> ma l (\a -> unEither (f a) l r))