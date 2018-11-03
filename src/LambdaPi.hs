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
  , mapBound
  , bitransverseScope
  )
import Bound.Var (Var(..), unvar)
import Control.Lens.Fold ((^?), preview)
import Control.Lens.Prism (Prism', prism')
import Control.Lens.Review (review)
import Control.Monad (ap, unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Trans.Class (lift)
import Data.Deriving (deriveShow1, deriveEq1)
import Data.Functor.Classes (Show1, Eq1(..))
import Data.Functor.Identity (Identity(..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))
import Data.Sequence ((|>), Seq, ViewL(..))

import qualified Bound.Scope as Bound
import qualified Data.Sequence as Seq

import Supply.Class

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
  fmap (unvar (\n -> if n == 0 then F a else B (n-1)) F) $
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
  -> a x -> a x
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

data CtxEntry a
  = Twin (Tm a) (Tm a)
  | Only (Tm a)
  deriving (Eq, Show)

data UnifyError a
  = Mismatch
  { errLhsTm :: Tm (Head a)
  , errLhsTy :: Tm (Head a)
  , errRhsTm :: Tm (Head a)
  , errRhsTy :: Tm (Head a)
  }
  | NotFound a
  | ExpectedTwin a
  | ExpectedOnly a
  deriving (Eq, Show)

getTwin
  :: (MonadError (UnifyError a) m, Eq a)
  => [(a, CtxEntry b)]
  -> a
  -> m (Tm b, Tm b)
getTwin ctx a = do
  a' <- maybe (throwError $ NotFound a) pure $ lookup a ctx
  case a' of
    Twin x y -> pure (x, y)
    _ -> throwError $ ExpectedTwin a

getOnly
  :: (MonadError (UnifyError a) m, Eq a)
  => [(a, CtxEntry b)]
  -> a
  -> m (Tm b)
getOnly ctx a = do
  a' <- maybe (throwError $ NotFound a) pure $ lookup a ctx
  case a' of
    Only x -> pure x
    _ -> throwError $ ExpectedOnly a

data Equation a
  = Equation
  { eqCtx :: [(a, CtxEntry (Head a))]
  , lhsTm :: Tm (Head a)
  , lhsTy :: Tm (Head a)
  , rhsTm :: Tm (Head a)
  , rhsTy :: Tm (Head a)
  }
  deriving (Eq, Show)

eta
  :: ( Eq a, Show a
     , MonadSupply a m
     , MonadError (UnifyError a) m
     )
  => Equation a -> m [Equation a]
eta (Equation ctx a (Pi 1 b c) a' (Pi 1 b' c')) = do
  x <- fresh
  pure
    [ Equation ((x, Twin b b') : ctx)
        (Neutral b  [Var $ VL x]) (Neutral (Lam 1 $ teleScope c ) [Var $ VL x])
        (Neutral b' [Var $ VR x]) (Neutral (Lam 1 $ teleScope c') [Var $ VR x])
    ]
eta (Equation ctx a (Pi n b c) a' (Pi n' b' c')) =
  error "TODO: telescoped pi types"
eta (Equation ctx a (Sigma b c) a' (Sigma b' c')) =
  pure
  [ Equation ctx
      aFst b
      aFst b'
  , Equation ctx
      (Neutral a  [Snd]) (Bound.instantiate1 aFst  c )
      (Neutral a' [Snd]) (Bound.instantiate1 a'Fst c')
  ]
  where
    aFst = Neutral a [Fst]
    a'Fst = Neutral a' [Fst]
-- TODO can this system solve universe constraints?
eta (Equation ctx Type Type Type Type) = pure []
eta (Equation ctx (Pi 1 a b) Type (Pi 1 a' b') Type) =
  pure
  [ Equation ctx
      a  Type
      a' Type
  , Equation ctx
      (Lam 1 $ teleScope b ) (Pi 1 a  $ liftTele Type)
      (Lam 1 $ teleScope b') (Pi 1 a' $ liftTele Type)
  ]
eta (Equation ctx (Pi n a b) Type (Pi n' a' b') Type) =
  error "TODO: telescoped pi types"
eta (Equation ctx (Sigma a b) Type (Sigma a' b') Type) =
  pure
  [ Equation ctx
      a  Type
      a' Type
  , Equation ctx
      (Lam 1 $ mapBound (const 0) b ) (Pi 1 a  $ liftTele Type)
      (Lam 1 $ mapBound (const 0) b') (Pi 1 a' $ liftTele Type)
  ]
eta (Equation ctx tm1@(Neutral (Var (V a)) bs) ty tm2@(Neutral (Var (V a')) bs') ty') = do
  aTy <- getOnly ctx a
  a'Ty <- getOnly ctx a'
  unless (a == a') .
    throwError $ Mismatch (Var $ V a) aTy (Var $ V a') a'Ty
  (Equation ctx aTy Type a'Ty Type :) <$>
    matchSpines ctx (aTy, tm1) (a'Ty, tm2)
eta (Equation ctx tm1@(Neutral (Var (VL a)) bs) ty tm2@(Neutral (Var (VL a')) bs') ty') = do
  (aTyL, _) <- getTwin ctx a
  (_, a'TyR) <- getTwin ctx a'
  unless (a == a') .
    throwError $ Mismatch (Var $ VL a) aTyL (Var $ VR a') a'TyR
  (Equation ctx aTyL Type a'TyR Type :) <$>
    matchSpines ctx (aTyL, tm2) (a'TyR, tm2)
eta (Equation _ a b a' b') = throwError $ Mismatch a b a' b'

matchSpines
  :: forall a m
   . (Show a, MonadError (UnifyError a) m)
  => [(a, CtxEntry (Head a))]
  -> (Tm (Head a), Tm (Head a))
  -> (Tm (Head a), Tm (Head a))
  -> m [Equation a]
matchSpines ctx (headTy, a1) (headTy', a2) = do
  (hd, as) <-
    maybe
      (error $ show a1 <> " is not a neutral term")
      pure
      (a1 ^? _Neutral)
  (hd', as') <-
    maybe
      (error $ show a2 <> " is not a neutral term")
      pure
      (a2 ^? _Neutral)
  go (headTy, Var hd, as) (headTy', Var hd', as')
  where
    go
      :: (Show a, MonadError (UnifyError a) m)
      => (Tm (Head a), Tm (Head a), Seq (Elim Tm (Head a)))
      -> (Tm (Head a), Tm (Head a), Seq (Elim Tm (Head a)))
      -> m [Equation a]
    go (ty, hd, as) (ty', hd', as') =
      case (Seq.viewl as, Seq.viewl as') of
        (EmptyL, EmptyL) -> pure []
        (x :< xs, y :< ys) ->
          case (ty, ty') of
            (Pi 1 a b, Pi 1 a' b') ->
              case (x, y) of
                (Elim_Tm c, Elim_Tm c') ->
                  (Equation ctx c a c' a' :) <$>
                  go
                    (instantiate (const c)  $ teleScope b , apply c  hd , xs)
                    (instantiate (const c') $ teleScope b', apply c' hd', ys)
                _ ->
                  error $
                  "spines don't match:\n\n" <>
                  show x <>
                  "\n\nand\n\n" <>
                  show y
            (Pi n a b, Pi n' a' b') ->
              error "TODO: telescoped pi types"
            (Sigma a b, Sigma a' b') ->
              case (x, y) of
                (Elim_Fst, Elim_Fst) ->
                  go
                    (a , elim hd  Elim_Fst, xs)
                    (a', elim hd' Elim_Fst, ys)
                (Elim_Snd, Elim_Snd) ->
                  go
                    ( Bound.instantiate1 (apply Fst hd ) b
                    , elim hd Elim_Snd
                    , xs
                    )
                    ( Bound.instantiate1 (apply Fst hd') b'
                    , elim hd' Elim_Snd
                    , ys
                    )
                _ ->
                  error $
                  "spines don't match:\n\n" <>
                  show x <>
                  "\n\nand\n\n" <>
                  show y
            _ ->
              error $
              "head types are not eliminatable:\n\n" <>
              show ty <>
              "\n\nand\n\n" <>
              show ty'
        -- failure cases? the paper says the spines must be the same length
        (_ :< _, EmptyL) ->
          error $
          "spines are different lengths:\n\n" <>
          show as <>
          "\n\nand\n\n" <> show as'
        (EmptyL, _ :< _) ->
          error $
          "spines are different lengths:\n\n" <>
          show as <>
          "\n\nand\n\n" <>
          show as'
