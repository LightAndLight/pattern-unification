{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
{-# language ViewPatterns #-}
module Unification where

import Bound.Scope (Scope, instantiate1, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Lens.Fold ((^?), (^..), folded, preview)
import Control.Lens.Review ((#), review)
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_1, _2)
import Control.Monad ((<=<), unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (StateT, modify)
import Control.Monad.Trans (MonadTrans, lift)
import Data.Bifunctor (Bifunctor(..))
import Data.Foldable (toList, foldl')
import Data.Maybe (fromMaybe)
import Data.Sequence ((<|), Seq, ViewL(..))

import qualified Bound.Scope as Bound
import qualified Data.Sequence as Seq

import Constraint
import LambdaPi
import Meta
import Supply.Class

varMeta :: Var b (Meta meta var) -> Meta meta (Var b var)
varMeta (B a) = N (B a)
varMeta (F (M a)) = M a
varMeta (F (N a)) = N (F a)

substMeta
  :: Tm (Var b (Meta meta var))
  -> (meta -> Tm (Meta meta var))
  -> Tm (Var b (Meta meta var))
substMeta tm f =
  tm >>= unvar (pure . B) (\case; M a -> F <$> f a; N a -> pure (F (N a)))

substMetaScope
  :: Eq meta
  => Solutions meta var
  -> Scope b Tm (Meta meta var)
  -> Tm (Var b (Meta meta var))
substMetaScope res t =
  substMeta
    (fromScope t)
    (\a -> fromMaybe (pure $ M a) $ lookupS res a)

trivial :: Applicative f => f (a -> Maybe b)
trivial = pure $ const Nothing

failure :: MonadTrans t => t Maybe a
failure = lift Nothing

singleton :: Eq a => a -> b -> (a -> Maybe b)
singleton a b = \x -> if x == a then Just b else Nothing

data TypeError a
  = NotInScope a
  | TypeMismatch (Tm a) (Tm a)

extendCtx
  :: Applicative m
  => Tm (Meta meta var)
  -> (c -> m (Tm (Meta meta var)))
  -> (Var () c -> m (Tm (Meta meta (Var () var))))
extendCtx b ctx =
  unvar
    (\() -> pure $ bimap id F <$> b)
    (over (mapped.mapped) (bimap id F) . ctx)

newtype Solutions meta var = Solutions [(meta, Tm (Meta meta var))]

merge
  :: (Eq meta, Show meta, Show var)
  => Solutions meta var
  -> Solutions meta var
  -> Solutions meta var
merge (Solutions s) (Solutions t) = Solutions $ go s t'
  where
    -- | Merge s and t. If s contains a solution that t doesn't provide,
    -- include it. If s contains a solution that t does provide, generate
    -- a constraint that their solutions are equal, and delete the solution
    -- from t
    go [] bs = bs
    go ((a, tm):as) bs =
      maybe
        ((a, tm) : go as bs)
        (\tm' -> error $ sameErr a tm tm')
        (lookup a bs)

    -- | Apply s to the rhs of t
    t' =
      over (mapped._2)
      (\tm ->
         tm >>= \v ->
          fromMaybe tm (v ^? _M >>= \v' -> lookup v' s))
      t

    sameErr x y z =
      "Same solution for " <> show x <>
      ": " <> show y <> " and " <> show z

instance Bifunctor Solutions where
  bimap f g (Solutions a) =
    Solutions $ fmap (bimap f (fmap (bimap f g))) a

lookupS :: Eq meta => Solutions meta var -> meta -> Maybe (Tm (Meta meta var))
lookupS (Solutions s) a = lookup a s

empty :: Solutions a b
empty = Solutions []

solve
  :: ( MonadError (TypeError (Meta meta var)) m
     , MonadSupply meta m
     , Show var
     , Eq var', Show var'
     , Eq meta, Show meta
     )
  => (var -> var')
  -> Constraint m meta var'
  -> m (Solutions meta var)
solve f (HasType ctx (normalize -> tm) (normalize -> ty)) =
  case (tm, ty) of
    (Type, t) -> solve f (Equals t Type)
    (Var (N a), t) -> do
      t' <- ctx a
      solve f (Equals t t')
    (Lam s, Pi b c) -> do
      -- gamma |- B : Type
      res0 <- solve f (HasType ctx b Type)

      -- gamma |- C : B -> Type
      res1 <- solve f (HasType ctx (Lam c) (Pi b (lift $ Type)))

      -- gamma, x : B |- y : C x
      res2 <-
        solve
          (F . f)
          (HasType
             (extendCtx b ctx)
             (varMeta <$> fromScope s)
             (varMeta <$> fromScope c))

      pure $ foldl' merge empty [res0, res1, res2]
solve f (Equals (normalize -> lhs) (normalize -> rhs)) =
  case (lhs, rhs) of
    -- tautologies
    (Type, Type) -> pure empty
    (Fst, Fst) -> pure empty
    (Snd, Snd) -> pure empty
    (Var (N a), Var (N b))
      | a == b -> pure empty
      | otherwise -> throwError $ TypeMismatch (_ lhs) (_ rhs)
    (Lam s, Lam s') ->
      solve
        (F . f)
        (Equals (varMeta <$> fromScope s) (varMeta <$> fromScope s'))
    (Pi s t, Pi s' t') -> do
      res0 <- solve f (Equals s s')
      res1 <-
        solve
        (F . f)
        (Equals
          (varMeta <$> substMetaScope (bimap id f res0) t)
          (varMeta <$> substMetaScope (bimap id f res0) t'))
      pure $ merge res0 res1

    -- pattern fragment
    (Neutral (Var (M a)) xs, _) -> _