{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope (fromScope)
import Data.Bifunctor (Bifunctor(..))

import LambdaPi

data Meta a b = M a | N b
  deriving (Eq, Show)

instance Functor (Meta a) where
  fmap _ (M a) = M a
  fmap f (N a) = N (f a)

instance Applicative (Meta a) where
  pure = N
  N f <*> N a = N (f a)
  M a <*> _ = M a
  _ <*> M a = M a

instance Bifunctor Meta where
  bimap f _ (M a) = M (f a)
  bimap _ g (N a) = N (g a)

data Solution a b = Solution a (Tm (Meta a b))

type TmM a b = Tm (Meta a b)

data Result a b
  = Postpone
  | Failure
  | Success (Maybe (Solution a b), Maybe (TmM a b))

occurs :: forall a b. (Eq a, Eq b) => a -> TmM a b -> Bool
occurs a tm =
  case tm of
    Var{} -> go False False tm
    Fst{} -> go False False tm
    Snd{} -> go False False tm
    Lam s -> go False False (sequenceA <$> fromScope s)
    Pair b c -> go False False b || go False False c
    Neutral (Var (M _)) cs -> any (go True False) cs
    Neutral (Var (N _)) cs -> any (go False True) cs
    Neutral _ cs -> any (go False False) cs
  where
    isVar Var{} = True
    isVar _ = False

    go :: forall c. (Eq a, Eq c) => Bool -> Bool -> TmM a c -> Bool
    go _ _ (Var (M b)) = a == b
    go _ _ (Var (N _)) = False
    go _ _ Fst{} = False
    go _ _ Snd{} = False
    go inMeta inVar (Lam s) = go inMeta inVar (sequenceA <$> fromScope s)
    go inMeta inVar (Pair d e) = go inMeta inVar d || go inMeta inVar e
    go inMeta inVar (Neutral (Var (M b)) cs)
      | a == b =
        if inVar
        then any ((||) <$> isVar <*> go True False) cs
        else
          if inMeta
          then any (go True False) cs
          else True
      | otherwise = any (go True False) cs
    go _ _ (Neutral (Var (N _)) cs) = any (go False True) cs
    go _ _ (Neutral _ cs) = any (go False False) cs

ex1 :: Bool
ex1 =
  occurs "alpha" $
  Var (N "x") .@ (Var (M "alpha") .@ Var (N "x"))

ex2 :: Bool
ex2 =
  occurs "beta" $
  Var (N "x") .@ (Var (M "beta") .@ lam (N "x") (Var $ N "x"))

solve :: (Eq a, Eq b) => TmM a b -> TmM a b -> Result a b
solve (Neutral (Var (M a)) xs) (Neutral (Var (M b)) ys)
  | a == b = _
  | otherwise = _
solve (Neutral (Var (M a)) xs) y = _
solve x (Neutral (Var (M b)) ys) = solve (Neutral (Var (M b)) ys) x
solve a b =
  if a == b
  then Success (Nothing, Nothing)
  else Failure
