{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language TemplateHaskell #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
module Tm where

import Bound.Scope (Scope, abstract1, instantiate1, fromScope, toScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Sequence ((|>), Seq, ViewL(..))

import qualified Data.Sequence as Seq

data Tm a
  = Var a
  | Type
  | App (Tm a) (Seq (Tm a))
  | Fst
  | Snd

  | Pi (Tm a) (Scope () Tm a)
  | Lam (Scope () Tm a)
  | Sigma (Tm a) (Scope () Tm a)
  | Pair (Tm a) (Tm a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Tm
deriveEq1 ''Tm
deriveShow1 ''Tm

deriving instance Eq a => Eq (Tm a)
deriving instance Show a => Show (Tm a)

(.@) :: Tm a -> Tm a -> Tm a
(.@) (App f xs) x = App f (xs |> x)
(.@) (Lam s) x = instantiate1 x s
(.@) (Pair a _) Fst = a
(.@) (Pair _ b) Snd = b
(.@) f x = App f $ Seq.singleton x

lam :: Eq a => a -> Tm a -> Tm a
lam a b = Lam $ abstract1 a b

pi :: Eq a => (a, Ty a) -> Ty a -> Ty a
pi (a, t) s = Pi t $ abstract1 a s

infixl 5 .@

type Ty = Tm

evalScope :: (a -> Ty a) -> Scope b Tm a -> Scope b Tm a
evalScope ctx = toScope . eval (unvar (pure . B) (fmap F . ctx)) . fromScope

eval :: forall a. (a -> Ty a) -> Tm a -> Tm a
eval ctx = go
  where
    go :: Tm a -> Tm a
    go e =
      case e of
        Var a -> go $ ctx a
        Type -> Type
        App f xs ->
          case Seq.viewl xs of
            a :< as ->
              case (go f, a) of
                (Pair _ v, Snd) -> go (App v as)
                (Pair v _, Fst) -> go (App v as)
                (Lam s, _) -> go (App (instantiate1 a s) as)
                _ -> error "eval: stuck"
            EmptyL -> go f
        Fst -> Fst
        Snd -> Snd

        Pi a s -> Pi (go a) (evalScope ctx s)
        Lam s -> Lam (evalScope ctx s)
        Sigma a s -> Sigma (go a) (evalScope ctx s)
        Pair a b -> Pair (go a) (go b)
