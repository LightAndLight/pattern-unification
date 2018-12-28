{-# language BangPatterns #-}
{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FunctionalDependencies, MultiParamTypeClasses #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language StandaloneDeriving, TemplateHaskell #-}
{-# language RankNTypes, ScopedTypeVariables #-}
{-# language QuantifiedConstraints #-}
module LambdaPi where

import Prelude hiding (pi)

import Bound.Class (Bound(..))
import Bound.Scope
  ( Scope(..)
  , abstract1, instantiate1
  , toScope, fromScope
  )
import Bound.Var (Var(..), unvar)
import Control.Lens.Fold (preview)
import Control.Lens.Prism (Prism', prism')
import Control.Lens.Review (review)
import Control.Monad (ap)
import Data.Bifunctor (Bifunctor(..), first)
import Data.Deriving (deriveShow1, deriveEq1)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Data.Sequence ((|>), Seq)
import Data.Traversable (foldMapDefault)
import Text.PrettyPrint.ANSI.Leijen (Doc, Pretty(..))

import qualified Text.PrettyPrint.ANSI.Leijen as Print


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
elim (Lam s) (Elim_Tm tm) = instantiate1 tm s
elim a b = error $ "can't eliminate " <> show a <> " with " <> show b

(.@) :: Tm a -> Tm a -> Tm a
(.@) (Lam a) b = instantiate1 b a
(.@) (Neutral a b) c = Neutral a $ b |> c
(.@) a b = Neutral a [b]

infixl 5 .@

data Tm a
  = Var a
  | Lam (Scope () Tm a)
  | Pair (Tm a) (Tm a)
  | Fst
  | Snd
  | Neutral (Tm a) (Seq (Tm a))
  deriving (Functor, Foldable, Traversable)

_Var :: Prism' (Tm a) a
_Var =
  prism'
    Var
    (\case
        Var a -> Just a
        _ -> Nothing)

deriveShow1 ''Tm; deriving instance Show a => Show (Tm a)
deriveEq1 ''Tm; deriving instance Eq a => Eq (Tm a)

instance Applicative Tm where; pure = return; (<*>) = ap
instance Monad Tm where
  return = Var

  Lam a >>= f = Lam (a >>>= f)
  Pair a b >>= f = Pair (a >>= f) (b >>= f)
  Fst >>= _ = Fst
  Snd >>= _ = Snd
  Neutral a bs >>= f = Neutral (a >>= f) ((>>= f) <$> bs)
  Var a >>= f = f a

lam :: Eq a => a -> Tm a -> Tm a
lam a = Lam . abstract1 a

lamM
  :: Eq c
  => c
  -> MetaT a b Tm c
  -> MetaT a b Tm c
lamM a =
  MetaT . Lam .
  toScope . fmap sequenceA . unMetaT . fromScope .
  abstract1 a

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
  => (a -> Maybe (Tm a))
  -> Scope b Tm a
  -> Scope b Tm a
evalScope ctx =
  toScope .
  eval (unvar (Just . pure . B) (fmap (fmap F) . ctx)) .
  fromScope

eval :: (Show a, Eq a) => (a -> Maybe (Tm a)) -> Tm a -> Tm a
eval ctx = go
  where
    go tm =
      case tm of
        Lam a -> Lam $ evalScope ctx a
        Pair a b -> Pair (go a) (go b)
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
        Var a -> fromMaybe tm $ ctx a

data Meta a b c
  = M a
  | L b
  | R b
  | N c
  deriving Show

instance (Eq a, Eq b, Eq c) => Eq (Meta a b c) where
  L a == R b = a == b
  R a == L b = a == b

  L a == L b = a == b
  R a == R b = a == b
  N a == N b = a == b
  M a == M b = a == b

  _ == _ = False

instance (Ord a, Ord b, Ord c) => Ord (Meta a b c) where
  L{} `compare` M{} = LT
  R{} `compare` M{} = LT
  M a `compare` M b = a `compare` b
  N{} `compare` M{} = GT

  L{} `compare` N{} = LT
  R{} `compare` N{} = LT
  M{} `compare` N{} = LT
  N a `compare` N b = a `compare` b

  R a `compare` L b = a `compare` b
  L a `compare` L b = a `compare` b
  M{} `compare` L{} = GT
  N{} `compare` L{} = GT

  L a `compare` R b = a `compare` b
  R a `compare` R b = a `compare` b
  M{} `compare` R{} = GT
  N{} `compare` R{} = GT

instance Foldable (Meta a b) where
  foldMap = foldMapDefault
instance Traversable (Meta a b) where
  sequenceA (M a) = pure (M a)
  sequenceA (L a) = pure (L a)
  sequenceA (R a) = pure (R a)
  sequenceA (N a) = N <$> a

instance Functor (Meta a b) where
  fmap _ (M a) = M a
  fmap _ (L a) = L a
  fmap _ (R a) = R a
  fmap f (N a) = N (f a)

instance Applicative (Meta a b) where
  pure = N
  N f <*> N a = N (f a)
  M a <*> _ = M a
  L a <*> _ = L a
  R a <*> _ = R a
  _ <*> M a = M a
  _ <*> L a = L a
  _ <*> R a = R a

instance Monad (Meta a b) where
  N a >>= f = f a
  L a >>= _ = L a
  R a >>= _ = R a
  M a >>= _ = M a

instance Bifunctor (Meta a) where
  bimap _ _ (M a) = M a
  bimap f _ (L a) = L (f a)
  bimap f _ (R a) = R (f a)
  bimap _ g (N a) = N (g a)

newtype MetaT a b m c = MetaT { unMetaT :: m (Meta a b c) }
deriving instance
  ( forall x. Eq x => Eq (m x)
  , Eq a
  , Eq b
  , Eq c
  )
  => Eq (MetaT a b m c)
deriving instance
  ( forall x. Show x => Show (m x)
  , Show a
  , Show b
  , Show c
  )
  => Show (MetaT a b m c)

instance Functor m => Functor (MetaT a b m) where
  fmap f (MetaT m) = MetaT $ fmap (fmap f) m
instance Applicative m => Applicative (MetaT a b m) where
  pure = MetaT . pure . pure
  MetaT a <*> MetaT b = MetaT $ (<*>) <$> a <*> b
instance Monad m => Monad (MetaT a b m) where
  MetaT ma >>= f = MetaT $ do
    a <- ma
    case a of
      N x -> unMetaT $ f x
      L x -> pure $ L x
      R x -> pure $ R x
      M x -> pure $ M x

instance Pretty a => Pretty (Tm a) where
  pretty = prettyTm pretty

instance (Pretty a, Pretty b, Pretty c) => Pretty (Meta a b c) where
  pretty = prettyMeta pretty pretty pretty

prettyMeta :: (a -> Doc) -> (b -> Doc) -> (c -> Doc) -> Meta a b c -> Doc
prettyMeta f _ _ (M a) = Print.text "?" <> f a
prettyMeta _ g _ (L a) = Print.text "<" <> g a
prettyMeta _ g _ (R a) = Print.text ">" <> g a
prettyMeta _ _ h (N a) = h a

prettyTm :: forall a. (a -> Doc) -> Tm a -> Doc
prettyTm aDoc = go Right
  where
    go :: forall b. (b -> Either Int a) -> Tm b -> Doc
    go ctx tm =
      case tm of
        Var a -> either Print.int aDoc $ ctx a
        Lam s ->
          Print.hsep
          [ Print.char 'λ' <> Print.dot
          , go (unvar (const $ Left 0) (first (+1) . ctx)) $ fromScope s
          ]
        Pair a b ->
          Print.hsep
          [ Print.char '〈'
          , go ctx a
          , Print.comma
          , go ctx b
          , Print.char '〉'
          ]
        Fst -> Print.text "fst"
        Snd -> Print.text "snd"
        Neutral x xs ->
          Print.hsep $
          [ go ctx x
          , Print.char '•'
          ] <>
          toList (go ctx <$> xs)
