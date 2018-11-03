{-# language BangPatterns #-}
{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FunctionalDependencies, MultiParamTypeClasses #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language StandaloneDeriving, TemplateHaskell #-}
{-# language RankNTypes, ScopedTypeVariables #-}
module LambdaPi where

import Prelude hiding (pi)

import Bound.Class (Bound(..))
import Bound.Scope
  ( Scope(..), unscope
  , abstract
  , instantiate
  , toScope, fromScope
  , bitransverseScope
  )
import Bound.Var (Var(..), unvar)
import Control.Lens.Fold (preview)
import Control.Lens.Prism (Prism', prism')
import Control.Lens.Review (review)
import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Data.Deriving (deriveShow1, deriveEq1)
import Data.Functor.Classes (Show1, Eq1(..))
import Data.Functor.Identity (Identity(..))
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Data.Sequence ((|>), Seq)

import qualified Bound.Scope as Bound

data Tele f a
  = More (Scope Int f a) (Tele f a)
  | Done (Scope Int f a)
  deriving (Functor, Foldable, Traversable)
deriveShow1 ''Tele; deriving instance (Show1 f, Show a) => Show (Tele f a)
instance (Monad f, Eq1 f) => Eq1 (Tele f) where
  liftEq f (Done a) (Done b) = liftEq f a b
  liftEq f (More a b) (More c d) = liftEq f a c && liftEq f b d
  liftEq _ _ _ = False
deriving instance (Monad f, Eq1 f, Eq a) => Eq (Tele f a)

liftTele :: Monad f => f a -> Tele f a
liftTele = Done . lift

teleScope :: Monad f => Tele f a -> Scope Int f a
teleScope (Done a) = a
teleScope (More _ a) = teleScope a

bitransverseTele
  :: forall m f g a b
   . Monad m
  => (forall x x'. (x -> m x') -> f x -> m (g x'))
  -> (a -> m b)
  -> Tele f a
  -> m (Tele g b)
bitransverseTele f g = go
  where
    go :: Tele f a -> m (Tele g b)
    go (Done s) = Done <$> bitransverseScope f g s
    go (More a b) = More <$> bitransverseScope f g a <*> go b

transverseTele
  :: (Monad m, Traversable g)
  => (forall x. f x -> m (g x))
  -> Tele f a
  -> m (Tele g a)
transverseTele f = bitransverseTele (\p -> (traverse p =<<) . f) pure

instantiate1 :: Functor f => f a -> Scope Int f a -> Scope Int f a
instantiate1 a =
  Scope .
  fmap (unvar (\n -> if n == 0 then F a else B (n-1)) F) .
  unscope

abstract1 :: (Eq a, Monad f) => a -> Scope Int f a -> Scope Int f a
abstract1 a =
  toScope .
  fmap (unvar (B . (+1)) (\a' -> if a == a' then B 0 else F a')) .
  fromScope

abstractTele
  :: (Eq a, Monad f)
  => a
  -> Tele f a
  -> Tele f a
abstractTele a = go
  where
    go tele =
      case tele of
        Done s -> Done $ abstract1 a s
        More b c -> More (abstract1 a b) (go c)

instantiateTele
  :: Monad f
  => f a
  -> Tele f a
  -> Either (f a) (f a, Tele f a)
instantiateTele tm tele =
  case tele of
    Done a -> Left $ goScope tm a
    More a b -> Right (goScope tm a, go tm b)
  where
    goScope
      :: Monad f
      => f a
      -> Scope Int f a
      -> f a
    goScope a =
      (>>= unvar (\n -> if n == 0 then a else undefined) pure) .
      fromScope

    go
      :: Monad f
      => f a
      -> Tele f a
      -> Tele f a
    go e (Done x) = Done $ instantiate1 e x
    go e (More x y) = More (instantiate1 e x) (go e y)

instance Bound Tele where
  Done a >>>= f = Done (a >>>= f)
  More a b >>>= f = More (a >>>= f) (b >>>= f)

data Elim f a
  = Elim_Tm (f a)
  | Elim_Fst
  | Elim_Snd
  deriving Show

instance Bound Elim where
  Elim_Tm a >>>= f = Elim_Tm (a >>= f)
  Elim_Fst >>>= _ = Elim_Fst
  Elim_Snd >>>= _ = Elim_Snd

class AsElim s f a | s -> f a where
  _Elim :: Prism' s (Elim f a)

  _Fst :: Prism' s ()
  _Fst = _Elim._Fst

  _Snd :: Prism' s ()
  _Snd = _Elim._Snd

  _Tm :: Prism' s (f a)
  _Tm = _Elim._Tm

instance AsElim (Elim f a) f a where
  _Elim = id

  _Fst =
    prism'
      (\() -> Elim_Fst)
      (\case
          Elim_Fst -> Just ()
          _ -> Nothing)

  _Snd =
    prism'
      (\() -> Elim_Snd)
      (\case
          Elim_Snd -> Just ()
          _ -> Nothing)

  _Tm =
    prism'
      Elim_Tm
      (\case
          Elim_Tm a -> Just a
          _ -> Nothing)

class AsNeutral s a | s -> a where
  _Neutral :: Prism' s (a, Seq (Elim Tm a))

elim :: Show a => Tm a -> Elim Tm a -> Tm a
elim (Pair a _) Elim_Fst = a
elim (Pair _ b) Elim_Snd = b
elim (Lam 0 s) tm = elim (instantiate undefined s) tm
elim (Lam n s) (Elim_Tm a) | n > 0 =
  Lam (n-1) .
  Scope .
  fmap (unvar (\m -> if m == 0 then F a else B (m-1)) F) $
  unscope s
elim a b = error $ "can't eliminate " <> show a <> " with " <> show b

apply :: Tm a -> Tm a -> Tm a
apply a (Lam 1 b) = instantiate (const a) b
apply a (Lam n b) = Lam (n-1) $ instantiate1 a b
apply a (Neutral b c) = Neutral b $ c |> a
apply a b = Neutral b [a]

data Head a = V a | VL a | VR a
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Tm a
  = Var a
  | Pi !Int (Tm a) (Tele Tm a)
  | Lam !Int (Scope Int Tm a)
  | Sigma (Tm a) (Scope () Tm a)
  | Pair (Tm a) (Tm a)
  | Fst
  | Snd
  | Type
  | Neutral (Tm a) (Seq (Tm a))
  deriving (Functor, Foldable, Traversable)

deriveShow1 ''Tm; deriving instance Show a => Show (Tm a)
deriveEq1 ''Tm; deriving instance Eq a => Eq (Tm a)

instance Applicative Tm where; pure = return; (<*>) = ap
instance Monad Tm where
  return = Var

  Pi n a b >>= f = Pi n (a >>= f) (b >>>= f)
  Lam n a >>= f = Lam n (a >>>= f)
  Sigma a b >>= f = Sigma (a >>= f) (b >>>= f)
  Pair a b >>= f = Pair (a >>= f) (b >>= f)
  Type >>= _ = Type
  Fst >>= _ = Fst
  Snd >>= _ = Snd
  Neutral a bs >>= f = Neutral (a >>= f) ((>>= f) <$> bs)
  Var a >>= f = f a

lam :: Eq a => [a] -> Tm a -> Tm a
lam args = Lam (length args) . abstract (`elemIndex` args)

sigma :: Eq a => (a, Tm a) -> Tm a -> Tm a
sigma (a, tm) tm' = Sigma tm (Bound.abstract1 a tm')

pi :: Eq a => (a, Tm a) -> [(a, Tm a)]-> Tm a -> Tm a
pi (a, tm) args ret =
  Pi (length args + 1) tm .
  abstractTele a $
  foldl
    (\tele (a', tm') -> More (lift tm') $ abstractTele a' tele)
    (Done $ lift ret)
    args

instance AsElim (Tm a) Tm a where
  _Elim =
    prism'
      (\case
          Elim_Tm a -> a
          Elim_Fst -> Fst
          Elim_Snd -> Snd)
      (\case
          Fst -> Just Elim_Fst
          Snd -> Just Elim_Snd
          a -> Just $ Elim_Tm a)

instance AsNeutral (Tm a) a where
  _Neutral =
    prism'
      (\(a, bs) -> Neutral (Var a) $ review _Elim <$> bs)
      (\case
          Neutral (Var a) bs -> (,) a <$> traverse (preview _Elim) bs
          _ -> Nothing)

evalScope
  :: ( Show a, Eq a
     , Show b, Eq b
     )
  => (a -> Tm a)
  -> Scope b Tm a
  -> Scope b Tm a
evalScope ctx =
  toScope .
  eval (unvar (pure . B) (fmap F . ctx)) .
  fromScope

evalTele :: (Show a, Eq a) => (a -> Tm a) -> Tele Tm a -> Tele Tm a
evalTele ctx (Done s) = Done $ evalScope ctx s
evalTele ctx (More s rest) = More (evalScope ctx s) (evalTele ctx rest)

bitransverseTm
  :: forall m a b
   . Monad m
  => (forall x x'. (x -> m x') -> Tm x -> m (Tm x'))
  -> (a -> m b)
  -> Tm a
  -> m (Tm b)
bitransverseTm f g = go
  where
    go :: Monad m => Tm a -> m (Tm b)
    go tm =
      case tm of
        Pi n a b -> Pi n <$> go a <*> bitransverseTele f g b
        Lam n a -> Lam n <$> bitransverseScope f g a
        Sigma a b -> Sigma <$> go a <*> bitransverseScope f g b
        Pair a b -> Pair <$> go a <*> go b
        Type -> pure Type
        Fst -> pure Fst
        Snd -> pure Snd
        Neutral a bs -> Neutral <$> go a <*> traverse go bs
        Var a -> Var <$> g a

transverseTm
  :: Monad m
  => (forall x. Tm x -> m (Tm x))
  -> Tm a
  -> m (Tm a)
transverseTm f = bitransverseTm (\p -> (traverse p =<<) . f) pure

plateTm
  :: Applicative m
  => (forall x. Tm x -> m (Tm x))
  -> Tm a -> m (Tm a)
plateTm f = go
  where
    goTele (Done a) = Done <$> goScope a
    goTele (More a b) = More <$> goScope a <*> goTele b

    goScope = fmap toScope . f . fromScope

    go tm =
      case tm of
        Pi n a b -> Pi n <$> f a <*> goTele b
        Lam n a -> Lam n <$> goScope a
        Sigma a b -> Sigma <$> f a <*> goScope b
        Pair a b -> Pair <$> f a <*> f b
        Neutral a bs -> Neutral <$> f a <*> traverse f bs
        _ -> f tm

{-
biplateTm
  :: forall m c a
   . (Monad m, c a, forall w z. (c w, c z) => c (Var w z))
  => Proxy c
  -> (forall c x. c x => Proxy c -> Tm x -> m (Tm x))
  -> (a -> m a)
  -> Tm a -> m (Tm a)
biplateTm pxy f g = go
  where
    goTele :: Tele Tm a -> m (Tele Tm a)
    goTele (Done a) = Done <$> goScope a
    goTele (More a b) = More <$> goScope a <*> goTele b

    goScope :: forall b. c (Var b a) => Scope b Tm a -> m (Scope b Tm a)
    goScope = fmap toScope . f pxy . fromScope

    go tm =
      case tm of
        Pi n a -> Pi n <$> goTele a
        Lam n a -> Lam n <$> goScope a
        Sigma a b -> Sigma <$> f pxy a <*> goScope b
        Pair a b -> Pair <$> f pxy a <*> f pxy b
        Neutral a bs -> Neutral <$> f pxy a <*> traverse (f pxy) bs
        _ -> traverse g =<< f pxy tm
-}

type Transversal s t a b =
  forall m
    . Applicative m
   => (forall x. a x -> m (b x))
   -> forall x. s x -> m (t x)

-- | Bottom-up transformation
transform
  :: Transversal a a a a
  -> (forall x. a x -> a x)
  -> a y -> a y
transform t f = go
  where
    go = f . runIdentity . t (Identity . f)

{-
eval :: (Show a, Eq a) => (forall x. Show x => x -> Tm x) -> Tm a -> Tm a
eval ctx =
  transform plateTm $
  \case
    Var a -> ctx a
    Neutral a bs ->
      let
        bs' =
          fromMaybe (error "non-eliminator in spine") $
          traverse (preview _Elim) bs
      in
        -- call by value
        foldl elim a bs'
    a -> a
-}

eval :: (Show a, Eq a) => (a -> Tm a) -> Tm a -> Tm a
eval ctx = go
  where
    go tm =
      case tm of
        Pi n a b -> Pi n (go a) (evalTele ctx b)
        Lam n a -> Lam n $ evalScope ctx a
        Sigma a b -> Sigma (go a) (evalScope ctx b)
        Pair a b -> Pair (go a) (go b)
        Type -> Type
        Fst -> Fst
        Snd -> Snd
        Neutral a bs ->
          let
            bs' =
              fromMaybe (error "non-eliminator in spine") $
              traverse (preview _Elim . go) bs
          in
            -- call by value
            foldl elim (go a) bs'
        Var a -> ctx a
