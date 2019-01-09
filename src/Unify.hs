{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Unify where

import Bound.Scope (abstract1, instantiate1)
import Control.Applicative (empty, liftA2)
import Control.Lens.Getter ((^.), uses)
import Control.Lens.Iso (iso)
import Control.Lens.Wrapped (Wrapped(..), Rewrapped, _Wrapped, _Unwrapped)
import Control.Lens.Setter ((%=))
import Control.Lens.TH (makeLenses)
import Control.Monad (guard)
import Control.Monad.Except (MonadError, ExceptT(..), runExceptT, throwError)
import Control.Monad.State (MonadState, StateT(..), evalStateT, gets, modify)
import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.Map (Map)
import Data.Sequence (Seq, ViewL(..), ViewR(..))
import Data.Set (Set)

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import Tm

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
  Meta a <*> b = Meta a
  TwinL a <*> b = TwinL a
  TwinR a <*> b = TwinR a
  Normal a <*> Meta b = Meta b
  Normal a <*> TwinL b = TwinL b
  Normal a <*> TwinR b = TwinR b
  Normal a <*> Normal b = Normal (a b)

instance Monad (Head a b) where
  Meta a >>= f = Meta a
  TwinL a >>= f = TwinL a
  TwinR a >>= f = TwinR a
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
        Meta a -> pure $ Meta a
        TwinL a -> pure $ TwinL a
        TwinR a -> pure $ TwinR a
        Normal a -> unHeadT $ f a

lt :: Applicative f => b -> f (Head a b c)
lt = pure . TwinL

rt :: Applicative f => b -> f (Head a b c)
rt = pure . TwinR

data Twin a b c = Twin (HeadT a b Ty c) (HeadT a b Ty c)
  deriving Functor

data Equation a b c
  = Equation
  { eqCtx :: Map b (Twin a b c)
  , eqLhsTm :: HeadT a b Tm c
  , eqLhsTy :: HeadT a b Ty c
  , eqRhsTm :: HeadT a b Tm c
  , eqRhsTy :: HeadT a b Ty c
  }

eta :: Equation a Int c -> [Equation a Int c]
eta (Equation ctx ltm lty rtm rty) =
  case (unHeadT ltm , unHeadT lty, unHeadT rtm, unHeadT rty) of
    (s, Pi a b, s', Pi a' b') ->
      [ Equation
          (Map.insert newVar (Twin (HeadT a) (HeadT a')) ctx)
          (HeadT $ s .@ lt newVar)
          (HeadT $ instantiate1 (lt newVar) b)
          (HeadT $ s' .@ rt newVar)
          (HeadT $ instantiate1 (rt newVar) b')
      ]
      where newVar = Map.size ctx
    (s, Sigma c d, s', Sigma c' d') ->
      [ Equation
          ctx
          (HeadT $ s .@ Fst)
          (HeadT c)
          (HeadT $ s' .@ Fst)
          (HeadT c')
      , Equation
          ctx
          (HeadT $ s .@ Snd)
          (HeadT $ instantiate1 (s .@ Fst) d)
          (HeadT $ s' .@ Snd)
          (HeadT $ instantiate1 (s' .@ Fst) d')
      ]
    _ -> []

data UnifyState a b c
  = UnifyState
  { _usSolutions :: Map a (HeadT a b Tm c)
  , _usMetas :: Map a (HeadT a b Ty c)
  }
makeLenses ''UnifyState

newtype UnifyM a b c x
  = UnifyM
  { unUnifyM
    :: StateT
         (UnifyState a b c)
         (Either (UnifyError a b c))
         x
  }
  deriving
    ( Functor, Applicative, Monad
    , MonadState (UnifyState a b c)
    , MonadError (UnifyError a b c)
    )

data UnifyError a b c
  = Mismatch (HeadT a b Tm c) (HeadT a b Tm c)
  | NotInScope (Head a b c)

lookupTwin
  :: (MonadError (UnifyError a b c) m, Ord b)
  => Either b b
  -> Map b (Twin a b c)
  -> m (HeadT a b Tm c)
lookupTwin (Left b) mp =
  case Map.lookup b mp of
    Just (Twin a _) -> pure a
    Nothing -> throwError $ NotInScope (TwinL b)
lookupTwin (Right b) mp =
  case Map.lookup b mp of
    Just (Twin _ a) -> pure a
    Nothing -> throwError $ NotInScope (TwinR b)

lookupMetaTy :: Ord a => a -> UnifyM a b c (HeadT a b Tm c)
lookupMetaTy a = do
  res <- uses usMetas $ Map.lookup a
  case res of
    Nothing -> throwError . NotInScope $ Meta a
    Just val -> pure val

decompose
  :: forall a b c
   . (Ord a, Ord b)
  => (c -> UnifyM a b c (HeadT a b Tm c))
  -> Map b (Twin a b c)
  -> (Tm (Head a b c), Seq (Tm (Head a b c)))
  -> (Tm (Head a b c), Seq (Tm (Head a b c)))
  -> UnifyM a b c (Maybe [Equation a b c])
decompose globals ctx (Var x, xs) (Var y, ys) = do
  xTy <- foldHead lookupMetaTy (getTwin . Left) (getTwin . Right) globals x
  yTy <- foldHead lookupMetaTy (getTwin . Left) (getTwin . Right) globals y
  Just <$> go (Var x) (unHeadT xTy) xs (Var y) (unHeadT yTy) ys
  where
    getTwin = flip lookupTwin ctx

    go
      :: Tm (Head a b c)
      -> Ty (Head a b c)
      -> Seq (Tm (Head a b c))

      -> Tm (Head a b c)
      -> Ty (Head a b c)
      -> Seq (Tm (Head a b c))

      -> UnifyM a b c [Equation a b c]
    go va tas as vb tbs bs =
      case (tas, Seq.viewl as, tbs, Seq.viewl bs) of
        (_, EmptyL, _, EmptyL) ->
          pure $
          [ Equation
              ctx
              (HeadT va)
              (HeadT tas)
              (HeadT vb)
              (HeadT tbs)
          ]
        (Sigma s _, Fst :< aas, Sigma s' _, Fst :< bbs) ->
          go
            (va .@ Fst) s aas
            (vb .@ Fst) s' bbs
        (Sigma _ t, Snd :< aas, Sigma _ t', Snd :< bbs) ->
          go
            (va .@ Snd) (instantiate1 (va .@ Fst) t) aas
            (vb .@ Snd) (instantiate1 (vb .@ Fst) t') bbs
        (Pi s t, aa :< aas, Pi s' t', bb :< bbs) ->
          (Equation
            ctx
            (HeadT aa)
            (HeadT s)
            (HeadT bb)
            (HeadT s') :) <$>
          go
            (va .@ aa) (instantiate1 aa t) aas
            (vb .@ bb) (instantiate1 bb t') bbs
        _ ->
          throwError $
          Mismatch
            (HeadT $ App (Var x) xs)
            (HeadT $ App (Var y) ys)
decompose _ _ _ _ = pure Nothing

distinctVars
  :: (Ord a, Ord b, Ord c)
  => Seq (Tm (Head a b c))
  -> Maybe (Seq (Either (Either b b) c))
distinctVars = flip evalStateT Set.empty . traverse f
  where
    f = \case
      Var Meta{} -> empty
      Var v -> do
        seen <- gets $ Set.member v
        guard $ not seen
        modify $ Set.insert v
        case v of
          Meta{} -> empty
          TwinL a -> pure $ Left (Left a)
          TwinR a -> pure $ Left (Right a)
          Normal a -> pure $ Right a
      _ -> empty

freeVars :: (Ord b, Ord c) => Tm (Head a b c) -> Set (Either (Either b b) c)
freeVars =
  foldr
    (foldHead
       (const id)
       (Set.insert . Left . Left)
       (Set.insert . Left . Left)
       (Set.insert . Right))
    Set.empty

flex
  :: forall a b c
   . (Ord a, Ord b, Ord c)
  => (c -> UnifyM a b c (HeadT a b Ty c))
  -> Equation a b c
  -> UnifyM a b c (Maybe [Equation a b c])
flex globals (Equation ctx ltm lty rtm rty) =
  case (unHeadT ltm, unHeadT rtm) of
    (App (Var (Meta x)) xs, App (Var (Meta y)) ys)
      | Just xs' <- distinctVars xs
      , Just ys' <- distinctVars ys
      -> flexFlex x xs' lty y ys' rty

    (App (Var (Meta x)) xs, y)
      | Just xs' <- distinctVars xs
      , all (`Set.member` freeVars y) xs'
      -> Just [] <$ flexRigid x xs' y (unHeadT rty)

    _ -> pure Nothing
  where
    toHead = either (either TwinL TwinR) Normal

    flexRigid
      :: a -> Seq (Either (Either b b) c)

      -> Tm (Head a b c) -> Ty (Head a b c)

      -> UnifyM a b c ()
    flexRigid meta xs y ty2 =
      case Seq.viewr xs of
        EmptyR -> usSolutions %= Map.insert meta (HeadT y)
        xxs :> xx -> do
          xxTy <- unHeadT <$> either (flip lookupTwin ctx) globals xx
          let headxx = toHead xx
          flexRigid
            meta
            xxs
            (Lam $ abstract1 headxx y) (Pi xxTy $ abstract1 headxx ty2)

    flexFlex = _

rigidRigid
  :: (Ord a, Ord b, Eq c)
  => (c -> UnifyM a b c (HeadT a b Tm c))
  -> Equation a b c
  -> UnifyM a b c [Equation a b c]
rigidRigid globals (Equation ctx ltm lty rtm rty) =
  case (unHeadT ltm, unHeadT lty, unHeadT rtm, unHeadT rty) of
    (Pi a b, Type, Pi a' b', Type) ->
      pure
      [ Equation
          ctx
          (HeadT a)
          (HeadT Type)
          (HeadT a')
          (HeadT Type)
      , Equation
          ctx
          (HeadT $ Lam b)
          (HeadT $ Pi Type (lift Type))
          (HeadT $ Lam b')
          (HeadT $ Pi Type (lift Type))
      ]
    (Sigma a b, Type, Sigma a' b', Type) ->
      pure
      [ Equation
          ctx
          (HeadT a)
          (HeadT Type)
          (HeadT a')
          (HeadT Type)
      , Equation
          ctx
          (HeadT $ Lam b)
          (HeadT $ Pi Type (lift Type))
          (HeadT $ Lam b')
          (HeadT $ Pi Type (lift Type))
      ]
    (App x xs, t, App y ys, t') -> do
      meqs <- decompose globals ctx (x, xs) (y, ys)
      case meqs of
        Nothing -> throwError $ Mismatch ltm rtm
        Just eqs ->
          pure $
          Equation
            ctx
            (HeadT t)
            (HeadT Type)
            (HeadT t')
            (HeadT Type) :
          eqs
    (Var a, t, Var b, t') | a == b ->
        pure
        [ Equation
            ctx
            (HeadT t)
            (HeadT Type)
            (HeadT t')
            (HeadT Type)
        ]
    -- woo
    (Type, Type, Type, Type) -> pure []
    _ -> throwError $ Mismatch ltm rtm
