{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
{-# language ViewPatterns #-}
module Unification where

import Prelude hiding (pi)
import Bound.Scope (Scope, fromScope)
import Bound.Var (Var(..), unvar)
import Control.Lens.Fold ((^?))
import Control.Lens.Setter (over, mapped)
import Control.Lens.Tuple (_2)
import Control.Monad.Except (MonadError, throwError, runExcept)
import Control.Monad.Trans (MonadTrans, lift)
import Data.Bifunctor (Bifunctor(..))
import Data.Foldable (foldl')
import Data.Maybe (fromMaybe)
import Data.Sequence ((<|), ViewR(..))

import qualified Data.Sequence as Seq

import Constraint
import LambdaPi
import Meta
import Supply.Class
import Supply

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

extendCtx
  :: Tm (Meta meta var)
  -> [(var, Tm (Meta meta var))]
  -> [(Var () var, Tm (Meta meta (Var () var)))]
extendCtx b ctx =
  ((B (), second F <$> b) : fmap (bimap F (fmap $ second F)) ctx)

newtype Solutions meta var = Solutions [(meta, Tm (Meta meta var))]
  deriving Show

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

singleton :: a -> Tm (Meta a b) -> Solutions a b
singleton a b = Solutions [(a, b)]

data TypeError meta var
  = NotInScope String
  | TypeMismatch String String
  | Can'tInfer String
  | Can'tSolve meta
  deriving Show

solve
  :: ( MonadError (TypeError meta (Meta meta var)) m
     , MonadSupply meta m
     , Show var
     , Eq var', Show var'
     , Eq meta, Show meta
     )
  => (var -> var')
  -> Constraint meta var'
  -> m (Solutions meta var)
solve f (HasType ctx (normalize -> tm) (normalize -> ty)) =
  case (tm, ty) of
    (Type, t) -> solve f (Equals t Type)
    (Var (N a), t) -> do
      t' <- maybe (throwError $ NotInScope (show a)) pure $ lookup a ctx
      solve f (Equals t t')
    (Neutral a bs, t) ->
      case Seq.viewr bs of
        EmptyR -> solve f (HasType ctx a t)
        bs' :> b -> do
          v <- fresh
          u <- fresh
          res0 <- solve f (HasType ctx (Neutral a bs') (Pi (Var $ M v) (pure $ M u)))
          case lookupS res0 v of
            Nothing -> throwError $ Can'tInfer (show $ Neutral a bs')
            Just v' -> do
              res1 <- solve f (HasType ctx b $ bimap id f <$> v')
              case lookupS (merge res0 res1) u of
                Nothing -> throwError $ Can'tSolve u
                Just u' -> solve f (Equals (Neutral (bimap id f <$> u') (b <| Seq.empty)) t)
    (Lam s, Pi b c) -> do
      -- gamma |- B : Type
      res0 <- solve f (HasType ctx b Type)

      -- gamma |- C : B -> Type
      -- gamma, x : B |- y : C x
      res1 <-
        solve
          (F . f)
          (HasType
             (extendCtx b ctx)
             (varMeta <$> fromScope c)
             Type)

      -- gamma, x : B |- y : C x
      res2 <-
        solve
          (F . f)
          (HasType
             (extendCtx b ctx)
             (varMeta <$> fromScope s)
             (varMeta <$> fromScope c))

      pure $ foldl' merge empty [res0, res1, res2]
    (Lam _, _) -> error "(Lam _, _)"
    (Pi s t, u) -> do
      res0 <- solve f (HasType ctx s Type)
      res1 <- solve f (HasType ctx (Lam t) (Pi s $ lift Type))
      res2 <- solve f (Equals u Type)
      pure $ foldl' merge empty [res0, res1, res2]
    (Var (M _), _) -> error "(Var (M m), _)"
      {-
      n <- M <$> fresh

      if we said ?m := ?n x_1 x_2 ... x_n    (for x_i in ctx)
      then some of the variables might escape their scope

      pure $
        singleton m
        (Neutral (Var n) (Seq.fromList $ _ $ Var . N . fst <$> ctx))
     -}
    (Sigma _ _, _) -> error "(Sigma _ _, _)"
    (Pair _ _, _) -> error "(Pair _ _, _)"
    (Fst, _) -> error "(Fst, _)"
    (Snd, _) -> error "(Snd, _)"
solve f (Equals (normalize -> lhs) (normalize -> rhs)) =
  case (lhs, rhs) of
    -- tautologies
    (Type, Type) -> pure empty
    (Type, _) -> throwError $ TypeMismatch (show lhs) (show rhs)
    (Fst, Fst) -> pure empty
    (Fst, _) -> throwError $ TypeMismatch (show lhs) (show rhs)
    (Snd, Snd) -> pure empty
    (Snd, _) -> throwError $ TypeMismatch (show lhs) (show rhs)
    (Var (N a), Var (N b))
      | a == b -> pure empty
      | otherwise -> throwError $ TypeMismatch (show lhs) (show rhs)
    (Var (N _), _) -> undefined
    (Lam s, Lam s') ->
      solve
        (F . f)
        (Equals (varMeta <$> fromScope s) (varMeta <$> fromScope s'))
    (Lam _, _) -> undefined
    (Pi s t, Pi s' t') -> do
      res0 <- solve f (Equals s s')
      res1 <-
        solve
        (F . f)
        (Equals
          (varMeta <$> substMetaScope (bimap id f res0) t)
          (varMeta <$> substMetaScope (bimap id f res0) t'))
      pure $ merge res0 res1
    (Pi _ _, _) -> undefined
    -- pattern fragment
    (Neutral (Var (M _)) _, _) -> undefined
    (Neutral _ _, _) -> undefined
    (Var (M _), _) -> undefined
    (Sigma _ _, _) -> undefined
    (Pair _ _, _) -> undefined

runSolve
  :: (Eq var, Show var)
  => Constraint Int var
  -> Either (TypeError Int (Meta Int var)) (Solutions Int var)
runSolve c = runExcept (runSupplyT 0 (\x -> (x, x+1)) (solve id c))

test_good :: Either (TypeError Int (Meta Int String)) (Solutions Int String)
test_good =
  runSolve
    (HasType
       []
       (lam (N "t") $ lam (N "x") $ Var $ N "x")
       (pi (N "t", Type) $ pi (N "x", Var $ N "t") $ Var (N "t")))

test_bad :: Either (TypeError Int (Meta Int String)) (Solutions Int String)
test_bad =
  runSolve
    (HasType
       []
       (lam (N "t") $ lam (N "x") $ Var $ N "x")
       (pi (N "t", Type) $ pi (N "x", Var $ N "t") $ Var (N "x")))
