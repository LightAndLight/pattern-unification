{-# language DeriveFunctor #-}
module Head where

import Control.Applicative (liftA2)

data Head a b c
  = Meta a
  | TwinL b
  | TwinR b
  | Normal c
  deriving (Functor, Show)

foldHead :: (a -> r) -> (b -> r) -> (b -> r) -> (c -> r) -> Head a b c -> r
foldHead a bl br c h =
  case h of
    Meta x -> a x
    TwinL x -> bl x
    TwinR x -> br x
    Normal x -> c x

instance (Eq a, Eq b, Eq c) => Eq (Head a b c) where
  Meta a == Meta b = a == b
  TwinL a == TwinL b = a == b
  TwinL a == TwinR b = a == b
  TwinR a == TwinL b = a == b
  TwinR a == TwinR b = a == b
  Normal a == Normal b = a == b
  _ == _ = False

instance (Ord a, Ord b, Ord c) => Ord (Head a b c) where
  compare (Meta a) (Meta b) = compare a b
  compare (TwinL a) (TwinL b) = compare a b
  compare (TwinL a) (TwinR b) = compare a b
  compare (TwinR a) (TwinL b) = compare a b
  compare (TwinR a) (TwinR b) = compare a b
  compare (Normal a) (Normal b) = compare a b

  compare Meta{} TwinL{} = LT
  compare Meta{} TwinR{} = LT
  compare Meta{} Normal{} = LT

  compare TwinL{} Meta{} = GT
  compare TwinL{} Normal{} = LT

  compare TwinR{} Meta{} = GT
  compare TwinR{} Normal{} = LT

  compare Normal{} Meta{} = GT
  compare Normal{} TwinL{} = GT
  compare Normal{} TwinR{} = GT

instance Applicative (Head a b) where
  pure = Normal
  Meta a <*> _ = Meta a
  TwinL a <*> _ = TwinL a
  TwinR a <*> _ = TwinR a
  Normal _ <*> Meta b = Meta b
  Normal _ <*> TwinL b = TwinL b
  Normal _ <*> TwinR b = TwinR b
  Normal a <*> Normal b = Normal (a b)

instance Monad (Head a b) where
  Meta a >>= _ = Meta a
  TwinL a >>= _ = TwinL a
  TwinR a >>= _ = TwinR a
  Normal a >>= f = f a

newtype HeadT a b m c = HeadT { unHeadT :: m (Head a b c) }
  deriving Functor

instance Applicative m => Applicative (HeadT a b m) where
  pure = HeadT . pure . pure
  HeadT a <*> HeadT b = HeadT $ liftA2 (<*>) a b

instance Monad m => Monad (HeadT a b m) where
  HeadT a >>= f =
    HeadT $ do
      a' <- a
      case a' of
        Meta b -> pure $ Meta b
        TwinL b -> pure $ TwinL b
        TwinR b -> pure $ TwinR b
        Normal b -> unHeadT $ f b

lt :: Applicative f => b -> f (Head a b c)
lt = pure . TwinL

rt :: Applicative f => b -> f (Head a b c)
rt = pure . TwinR