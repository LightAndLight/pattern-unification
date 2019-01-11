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

import Prelude hiding (pi)

import Bound.Scope (Scope, instantiate1, fromScope)
import Bound.Var (unvar)
import Control.Applicative (empty)
import Control.Lens.Getter (uses, use)
import Control.Lens.Setter ((%=))
import Control.Lens.TH (makeLenses)
import Control.Monad (guard)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, StateT(..), evalStateT, gets, modify)
import Control.Monad.Trans.Class (lift)
import Data.Map (Map)
import Data.Sequence ((|>), Seq, ViewL(..), ViewR(..))
import Data.Set (Set)

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import Tm
import Head

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
  , _usSupply :: a
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

freshMeta :: Enum a => UnifyM a b c a
freshMeta = do
  a <- use usSupply
  usSupply %= succ
  pure a

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
          pure
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
   . (Ord a, Enum a, Ord b, Ord c)
  => (c -> UnifyM a b c (HeadT a b Ty c))
  -> Equation a b c
  -> UnifyM a b c (Maybe [Equation a b c])
flex globals (Equation ctx ltm lty rtm rty) =
  case (unHeadT ltm, unHeadT rtm) of
    (App (Var (Meta x)) xs, App (Var (Meta y)) ys)
      | Just xs' <- distinctVars xs
      , Just ys' <- distinctVars ys
      ->
        if x == y
        then do
          newMeta <- freshMeta
          flexFlexSame x xs' (unHeadT lty) ys' (unHeadT rty) newMeta mempty id
        else
          -- flexFlex with different metas. to be written.
          -- it's not in gundry's thesis.. why?
          pure Nothing
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
            (lam headxx y) (pi (headxx, xxTy) ty2)

    ltyFreeVars = freeVars $ unHeadT lty
    rtyFreeVars = freeVars $ unHeadT rty

    flexFlexSame
      :: a
      -> Seq (Either (Either b b) c) -> Ty (Head a b c)
      -> Seq (Either (Either b b) c) -> Ty (Head a b c)
      -> a -> Seq (Either (Either b b) c) -> (Tm (Head a b c) -> Tm (Head a b c))
      -> UnifyM a b c (Maybe [Equation a b c])
    flexFlexSame meta xs xty ys yty newMeta vs newTm =
      case (Seq.viewr xs, Seq.viewr ys) of
        (EmptyR, EmptyR) -> do
          usMetas %=
            Map.insert newMeta (HeadT xty)
          usSolutions %=
            Map.insert meta (HeadT $ foldr (lam . toHead) (newTm . Var $ Meta newMeta) vs)
          pure $ Just [ Equation ctx (HeadT xty) (HeadT Type) (HeadT yty) (HeadT Type) ]
        (xxs :> xx, yys :> yy) -> do
          xxTy <- unHeadT <$> either (flip lookupTwin ctx) globals xx
          yyTy <- unHeadT <$> either (flip lookupTwin ctx) globals yy
          if xx == yy
            then
              -- these variables will be included and we don't care whether or not
              -- the target type depends on them
              flexFlexSame
                meta
                xxs (pi (toHead xx, xxTy) xty)
                yys (pi (toHead yy, yyTy) yty)
                newMeta (vs |> xx) (\tm -> tm .@ Var (toHead xx))
            else
              if
                -- since we're going to ignore these variables, we need to check
                -- that the target type doesn't depend on them
                xx `Set.notMember` ltyFreeVars &&
                yy `Set.notMember` rtyFreeVars
              then
                flexFlexSame
                  meta
                  xxs (Pi xxTy $ lift xty)
                  yys (Pi yyTy $ lift yty)
                  newMeta vs (\tm -> tm .@ Var (toHead xx))
              else
                pure Nothing
        _ -> throwError $ Mismatch ltm rtm

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

rigidVars
  :: forall a b c
   . (Ord a, Ord b, Ord c)
  => Tm (Head a b c)
  -> Set (Head a b c)
rigidVars = go False Just
  where
    goScope
      :: forall x w
       . Bool
      -> (x -> Maybe (Head a b c))
      -> Scope w Tm x
      -> Set (Head a b c)
    goScope underMeta toVar s =
      go underMeta (unvar (const Nothing) toVar) (fromScope s)

    go :: forall x. Bool -> (x -> Maybe (Head a b c)) -> Tm x -> Set (Head a b c)
    go underMeta toVar tm =
      case tm of
        Var a ->
          if underMeta
          then Set.empty
          else maybe Set.empty Set.singleton $ toVar a
        Type -> Set.empty
        App x xs ->
          go underMeta toVar x <>
          case x of
            Var a ->
              foldMap
                (go (maybe underMeta (\case; Meta{} -> True; _ -> underMeta) $ toVar a) toVar)
                xs
            _ ->
              foldMap (go underMeta toVar) xs
        Fst -> Set.empty
        Snd -> Set.empty
        Pi s t ->
          go underMeta toVar s <>
          goScope underMeta toVar t
        Lam s ->
          goScope underMeta toVar s
        Sigma s t ->
          go underMeta toVar s <>
          goScope underMeta toVar t
        Pair a b ->
          go underMeta toVar a <>
          go underMeta toVar b