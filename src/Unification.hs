{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Unification where

import Bound.Scope
  ( instantiate
  , fromScope
  , mapBound
  )
import Bound.Var (unvar)
import Control.Lens.Fold ((^?), (^..), folded, preview)
import Control.Lens.Prism (_Just)
import Control.Lens.Review ((#), review)
import Control.Lens.Tuple (_1, _2)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)
import Data.Foldable (toList, foldl')
import Data.Sequence (Seq, ViewL(..))

import qualified Bound.Scope as Bound
import qualified Data.Sequence as Seq

import Equation
import LambdaPi
import Supply.Class
import Solver.Class

data UnifyError f a
  = Mismatch
  { errLhsTm :: Tm (f a)
  , errLhsTy :: Tm (f a)
  , errRhsTm :: Tm (f a)
  , errRhsTy :: Tm (f a)
  }
  | NotFound a
  | ExpectedTwin a
  | ExpectedOnly a
  deriving (Eq, Show)

getTwin
  :: (MonadError (UnifyError f a) m, Eq a)
  => [(a, CtxEntry (f a))]
  -> a
  -> m (Tm (f a), Tm (f a))
getTwin ctx a = do
  a' <- maybe (throwError $ NotFound a) pure $ lookup a ctx
  case a' of
    Twin x y -> pure (x, y)
    _ -> throwError $ ExpectedTwin a

getOnly
  :: (MonadError (UnifyError f a) m, Eq a)
  => [(a, CtxEntry (f a))]
  -> a
  -> m (Tm (f a))
getOnly ctx a = do
  a' <- maybe (throwError $ NotFound a) pure $ lookup a ctx
  case a' of
    Only x -> pure x
    _ -> throwError $ ExpectedOnly a

eta
  :: ( Eq a, Show a
     , MonadSupply a m
     , MonadError (UnifyError Meta a) m
     )
  => Equation Meta a -> m [Equation Meta a]
eta (Equation ctx a (Pi 1 b c) a' (Pi 1 b' c')) = do
  x <- fresh
  pure
    [ Equation ((x, Twin b b') : ctx)
        (apply (Var $ _VL # x) a ) (apply (Var $ _VL # x) (Lam 1 $ teleScope c ))
        (apply (Var $ _VR # x) a') (apply (Var $ _VR # x) (Lam 1 $ teleScope c'))
    ]
eta (Equation _ _ Pi{} _ Pi{}) = error "TODO: telescoped pi types"
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
eta (Equation _ Type Type Type Type) = pure []
eta (Equation ctx (Pi 1 a b) Type (Pi 1 a' b') Type) =
  pure
  [ Equation ctx
      a  Type
      a' Type
  , Equation ctx
      (Lam 1 $ teleScope b ) (Pi 1 a  $ liftTele Type)
      (Lam 1 $ teleScope b') (Pi 1 a' $ liftTele Type)
  ]
eta (Equation _ Pi{} Type Pi{} Type) =
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
eta (Equation ctx tm1@(Neutral v _) _ tm2@(Neutral v' _) _)
  | Just a <- v ^? _Var._V
  , Just a' <- v' ^? _Var._V = do
  aTy <- getOnly ctx a
  a'Ty <- getOnly ctx a'
  unless (a == a') .
    throwError $ Mismatch (Var $ _V # a) aTy (Var $ _V # a') a'Ty
  (Equation ctx aTy Type a'Ty Type :) <$>
    matchSpines ctx (aTy, tm1) (a'Ty, tm2)
eta (Equation ctx tm1@(Neutral v _) _ tm2@(Neutral v' _) _)
  | Just a <- v ^? _Var._VL
  , Just a' <- v' ^? _Var._VR = do
    (aTyL, _) <- getTwin ctx a
    (_, a'TyR) <- getTwin ctx a'
    unless (a == a') .
      throwError $ Mismatch (Var $ _VL # a) aTyL (Var $ _VR # a') a'TyR
    (Equation ctx aTyL Type a'TyR Type :) <$>
      matchSpines ctx (aTyL, tm1) (a'TyR, tm2)
eta (Equation _ a b a' b') = throwError $ Mismatch a b a' b'

matchSpines
  :: forall a m
   . (Show a, MonadError (UnifyError Meta a) m)
  => [(a, CtxEntry (Meta a))]
  -> (Tm (Meta a), Tm (Meta a))
  -> (Tm (Meta a), Tm (Meta a))
  -> m [Equation Meta a]
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
      :: (Show a, MonadError (UnifyError Meta a) m)
      => (Tm (Meta a), Tm (Meta a), Seq (Elim Tm (Meta a)))
      -> (Tm (Meta a), Tm (Meta a), Seq (Elim Tm (Meta a)))
      -> m [Equation Meta a]
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
            (Pi{}, Pi{}) -> error "TODO: telescoped pi types"
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

-- | @a \`linearOn\` b@ means:
--
-- @forall x. x `elem` b ==> length (filter (==x) b) == length (filter (==x) a)@
linearOn :: (Eq a, Foldable f, Foldable g) => f a -> g a -> Bool
linearOn a b =
  all (\x -> count x b == count x a) b
  where
    count :: (Eq a, Foldable f) => a -> f a -> Int
    count c = foldl' (\acc x -> if x == c then acc + 1 else acc) 0

strongRigidIn :: Eq a => a -> Tm (Meta a) -> Bool
strongRigidIn a = go (== M a) False
  where
    goTele f (Done s) = goScope f s
    goTele f (More s t) = goScope f s || goTele f t

    goScope f s = go (unvar (const False) f) False $ fromScope s

    go :: (Eq a, Eq (f a)) => (f a -> Bool) -> Bool -> Tm (f a) -> Bool
    go f inSpine tm =
      case tm of
        Pi _ b c -> go f False b || goTele f c
        Lam _ b -> goScope f b
        Sigma b c -> go f False b || goScope f c
        Pair b c -> go f False b || go f False c
        Neutral b cs -> go f False b || any (go f True) cs
        Var b -> not inSpine && f b
        Type -> False
        Fst -> False
        Snd -> False

flexRigid
  :: ( Eq a, Show a
     , MonadSupply a m
     , AsSolverError e a, MonadError e m
     , MonadSolver a m
     )
  => m ()
flexRigid = do
  md <- preview (_Just._MetaDecl._1) <$> lookLeft
  p <- currentProblem
  case (md, p) of
    (Just a, Just (Problem sig eq))
      | Equation ctx tm ty tm' ty' <- eq ->
        case tm ^? _Neutral of
          Just (M a', xs)
            | strongRigidIn a' tm' -> throwError $ _Occurs # (M a', tm')
            | a == a'
            , Just xs' <- traverse (preview $ _Tm._Var._V) xs
            , notElem a $ (sig ^.. folded._2.folded._M) <> (tm' ^.. folded._M)
            , xs' `linearOn` (tm' ^.. folded._V)
            , all (`notElem` tm ^.. folded._V) (fmap fst ctx) -> do
                solve a (lam (review _V <$> toList xs') $ tm')
                dissolve
          _ -> do
            l <- lookLeft
            case l of
              Nothing -> pure ()
              Just MetaProblem{} -> swapLeft
              Just (MetaDecl b _) ->
                if
                  b `elem`
                  (sig ^.. folded._2.folded._M) <>
                  (ctx ^.. folded._2.folded._M) <>
                  (tm ^.. folded._M) <>
                  (ty ^.. folded._M) <>
                  (tm' ^.. folded._M) <>
                  (ty' ^.. folded._M)
                then
                  case tm ^? _Neutral._1._M of
                    Nothing -> expandSig
                    Just{} -> pure ()
                else swapLeft
    _ -> pure ()
