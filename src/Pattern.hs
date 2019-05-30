{-# language BangPatterns #-}
{-# language DeriveFunctor, DeriveFoldable #-}
{-# language LambdaCase #-}
{-# language RankNTypes #-}
{-# language QuantifiedConstraints #-}
module Pattern where

import Debug.Trace

import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Data.Coerce (Coercible, coerce)
import Data.Deriving (deriveEq1, deriveShow1, makeLiftEq)
import Data.Functor.Classes (Eq1(..), eq1, showsPrec1)
import Data.Functor.Product (Product)
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Set (Set)
import Data.Sequence (Seq, (<|))
import Data.Text (Text)
import Data.Vector (Vector)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.Vector as Vector

data Tele a =
  Tele
    -- 0 free vars
    Text (Tm a)
    -- `i`th element has i+1 free variables
    (Vector (Text, Tm a))
  deriving (Eq, Show, Functor, Foldable)

teleSize :: Tele a -> Int
teleSize (Tele _ _ v) = Vector.length v + 1

consTele :: Text -> Tm a -> Tele a -> Tele a
consTele a b (Tele x y z) = Tele a b $ Vector.cons (x, y) z

data V
  = M Int
  | S Int
  | TL Int
  | TR Int
  deriving (Eq, Ord, Show)

data Tm a
  = Var a

  | Bound Int
  | Ann (Tm a) (Tm a)

  | Type

  --   t    (teleSize t) free vars
  | Pi (Tele a) (Tm a)
  --         1 free var
  | Lam Text (Tm a)
  | App (Tm a) (Tm a)

  --                  1 free var
  | Sigma Text (Tm a) (Tm a)
  | Pair (Tm a) (Tm a)
  | Fst (Tm a)
  | Snd (Tm a)
  deriving (Eq, Show, Functor, Foldable)

type Ty = Tm

rho ::
  -- i
  Int ->
  -- Fin m -> Fin m
  (Int -> Int) ->
  -- Fin (i + m) -> Fin (i + n)
  Int -> Int
rho i f n
  | n < i = n
  | n >= i = f (n-i) + i

renameTele ::
  -- Fin m -> Fin n
  (Int -> Int) ->
  -- Tele m
  Tele a ->
  -- Tele n
  Tele a
renameTele f (Tele n s ts) =
  Tele n
    (rename f s)
    (Vector.imap (\i (nn, tt) -> (nn, rename (rho (i+1) f) tt)) ts)

--        (Fin m -> Fin n) -> Tm m -> Tm n
rename :: (Int -> Int) -> Tm a -> Tm a
rename f tm =
  case tm of
    Var a -> Var a
    Bound a -> Bound (f a)
    Ann a b -> Ann (rename f a) (rename f b)
    Type -> Type
    Pi tele a -> Pi (renameTele f tele) (rename (rho (teleSize tele) f) a)
    Lam n a -> Lam n $ rename (rho 1 f) a
    App a b -> App (rename f a) (rename f b)
    Sigma n s t -> Sigma n (rename f s) (rename (rho 1 f) t)
    Pair a b -> Pair (rename f a) (rename f b)
    Fst a -> Fst $ rename f a
    Snd a -> Snd $ rename f a

sig ::
  -- i
  Int ->
  -- Fin m -> Tm n
  (Int -> Tm a) ->
  -- Fin (i + m) -> Tm (i + n)
  Int -> Tm a
sig i f n
  | n < i = Bound n
  | n >= i = rename (+i) $ f (n-i)

substTele ::
  -- Fin m -> Fin n
  (Int -> Tm a) ->
  -- Tele m
  Tele a ->
  -- Tele n
  Tele a
substTele f (Tele n s ts) =
  Tele n
    (subst f s)
    (Vector.imap (\i (nn, tt) -> (nn, subst (sig (i+1) f) tt)) ts)

--       (Fin m -> Tm n) -> Tm m -> Tm n
subst :: (Int -> Tm a) -> Tm a -> Tm a
subst f tm =
  case tm of
    Var a -> Var a
    Bound a -> f a
    Ann a b -> Ann (subst f a) (subst f b)
    Type -> Type
    Pi tele a -> Pi (substTele f tele) $ subst (sig (teleSize tele) f) a
    Lam n a -> Lam n $ subst (sig 1 f) a
    App a b -> App (subst f a) (subst f b)
    Sigma n s t -> Sigma n (subst f s) $ subst (sig 1 f) t
    Pair a b -> Pair (subst f a) (subst f b)
    Fst a -> Fst $ subst f a
    Snd a -> Snd $ subst f a

inst ::
  -- Tm (suc n)
  Tm a ->
  -- Tm n
  Tm a ->
  -- Tm n
  Tm a
inst a b = subst (\case; 0 -> b; n -> Bound (n-1)) a

abstractD :: Eq a => (a -> Maybe Int) -> Int -> Tm a -> Tm a
abstractD f = go
  where
    go !depth tm =
      case tm of
        Var a -> maybe (Var a) (Bound . (depth+)) (f a)
        Bound a -> Bound $! if a >= depth then a+1 else a
        Ann a b -> Ann (go depth a) (go depth b)
        Type -> Type
        Pi tele a ->
          Pi
            (abstractDTele f depth tele)
            (go (depth+teleSize tele) a)
        Lam n a -> Lam n (go (depth+1) a)
        App a b -> App (go depth a) (go depth b)
        Sigma n s t ->
          Sigma n (go depth s) (go (depth+1) t)
        Pair a b -> Pair (go depth a) (go depth b)
        Fst a -> Fst $ go depth a
        Snd a -> Snd $ go depth a

abstractDTele :: Eq a => (a -> Maybe Int) -> Int -> Tele a -> Tele a
abstractDTele f !depth (Tele n s ts) =
  Tele n
    (abstractD f depth s)
    (Vector.imap (\i (nn, tt) -> (nn, abstractD f (depth+i+1) tt)) ts)

abstract :: Eq a => (a -> Maybe Int) -> Tm a -> Tm a
abstract f = abstractD f 0

abstract1 ::
  Eq a =>
  a ->
  -- Tm n
  Tm a ->
  -- Tm (suc n)
  Tm a
abstract1 a =
  abstract (\x -> if a == x then Just 0 else Nothing)

abstractTele :: Eq a => (a -> Maybe Int) -> Tele a -> Tele a
abstractTele f = abstractDTele f 0

abstractTele1 ::
  Eq a =>
  a ->
  -- Tm n
  Tele a ->
  -- Tm (suc n)
  Tele a
abstractTele1 a =
  abstractTele (\x -> if a == x then Just 0 else Nothing )

unfoldApps :: Tm a -> (Tm a, [Tm a])
unfoldApps = go []
  where
    go bs (App a b) = go (b : bs) a
    go bs a = (a, bs)

pi_ ::
  [(Text, Ty Text)] ->
  Ty Text ->
  Ty Text
pi_ = go []
  where
    go names [] b = abstractD (`elemIndex` names) 0 b
    go names ((n, t) : as) b =
      case go (n : names) as b of
        Pi tele b' -> Pi (consTele n t $ abstractTele1 n tele) b'
        b' -> Pi (Tele n t mempty) b'

piV_ ::
  [(Text, TyV Text)] ->
  TyV Text ->
  TyV Text
piV_ = go []
  where
    go names [] b = abstractD (`elemIndex` names) 0 b
    go names ((n, t) : as) b =
      case go (Right n : names) as b of
        Pi tele b' -> Pi (consTele n t $ abstractTele1 (Right n) tele) b'
        b' -> Pi (Tele n t mempty) b'

lam_ :: Text -> Tm Text -> Tm Text
lam_ n = Lam n . abstract1 n

sigma_ :: (Text, Ty Text) -> Ty Text -> Ty Text
sigma_ (n, s) = Sigma n s . abstract1 n

data TypeError a
  = NotInScope a
  | Unbound Int
  | ExpectedPi (Tm a)
  | ExpectedSigma (Tm a)
  | TypeIsTypeNot (Tm a)
  | PiIsTypeNot (Tm a)
  | LamIsPiNot (Tm a)
  | SigmaIsTypeNot (Tm a)
  | PairIsSigmaNot (Tm a)
  | Can'tInfer (Tm a)
  | TypeMismatch (Tm a) (Tm a)
  deriving (Eq, Show)

check ::
  Ord a =>
  Map a (Ty a) ->
  Seq Text ->
  Seq (Ty a) ->
  Tm a ->
  Ty a ->
  Either (TypeError a) ()
check nameCtx names ctx tm ty =
  case tm of
    Type ->
      case ty of
        Type -> pure ()
        _ -> Left $ TypeIsTypeNot ty

    Pi (Tele n s rest) t ->
      case ty of
        Type -> do
          () <- check nameCtx names ctx s Type
          case Vector.length rest of
            0 ->
              check nameCtx (n <| names) (s <| ctx) t Type
            _ ->
              check
                nameCtx
                (n <| names)
                (s <| ctx)
                (Pi (uncurry Tele (Vector.head rest) (Vector.tail rest)) t)
                Type
        _ -> Left $ PiIsTypeNot ty

    Lam _ e ->
      case ty of
        Pi (Tele n s rest) t ->
          check nameCtx (n <| names) (rename (+1) <$> s <| ctx) e $
          case Vector.length rest of
            0 -> t
            _ -> Pi (uncurry Tele (Vector.head rest) (Vector.tail rest)) t
        _ -> Left $ LamIsPiNot ty

    Sigma n s t ->
      case ty of
        Type -> do
          () <- check nameCtx names ctx s Type
          check nameCtx (n <| names) (s <| ctx) t Type
        _ -> Left $ SigmaIsTypeNot ty

    Pair a b ->
      case ty of
        Sigma _ s t -> do
          () <- check nameCtx names ctx a s
          check nameCtx names ctx b (inst t a)
        _ -> Left $ PairIsSigmaNot ty

    _ -> do
      ty' <- infer nameCtx names ctx tm
      if ty == ty'
        then pure ()
        else Left $ TypeMismatch ty ty'

infer ::
  Ord a =>
  Map a (Ty a) ->
  Seq Text ->
  Seq (Ty a) ->
  Tm a ->
  Either (TypeError a) (Tm a)
infer nameCtx names ctx tm =
  case tm of
    Var n ->
      case Map.lookup n nameCtx of
        Nothing -> Left $ NotInScope n
        Just ty -> pure ty

    Bound a ->
      case ctx Seq.!? a of
        Nothing -> Left $ Unbound a
        Just ty -> traceShow ((() <$) <$> ctx, () <$ ty) $ pure ty

    App f x -> do
      fTy <- infer nameCtx names ctx f
      case fTy of
        Pi (Tele _ s rest) t -> do
          () <- check nameCtx names ctx x s
          pure $
            inst
            (case Vector.length rest of
               0 -> t
               _ -> Pi (uncurry Tele (Vector.head rest) (Vector.tail rest)) t)
            x
        _ -> Left $ ExpectedPi fTy

    Fst a -> do
      aTy <- infer nameCtx names ctx a
      case aTy of
        Sigma _ x _ -> pure x
        _ -> Left $ ExpectedSigma aTy

    Snd a -> do
      aTy <- infer nameCtx names ctx a
      case aTy of
        Sigma _ _ y -> pure $ inst y (Fst a)
        _ -> Left $ ExpectedSigma aTy

    Ann a t -> t <$ check nameCtx names ctx a t
    _ -> Left $ Can'tInfer tm

data Equation a =
  Equation
  { _eqTmL :: Tm (Either V a)
  , _eqTyL :: Ty (Either V a)
  , _eqTmR :: Tm (Either V a)
  , _eqTyR :: Ty (Either V a)
  }
  deriving (Eq, Show)

type TmV a = Tm (Either V a)
type TyV a = TmV a

data Entry a
  = Twin (TyV a) (TyV a)
  | Single (TyV a)
  deriving (Eq, Show)

data Problem a
  = Problem
  { _pScope :: Seq (Entry a)
  , _pEquation :: Equation a
  } deriving (Eq, Show)

fmv :: TmV a -> Set Int
fmv = foldr (either (\case; M a -> Set.insert a; _ -> id) (const id)) mempty

fv :: Ord a => TmV a -> Set (Either V a)
fv = foldr Set.insert mempty

fv_rig :: Ord a => TmV a -> Set (Either V a)
fv_rig = go False
  where
    goTele (Tele _ a as) = go False a <> foldMap (go False . snd) as
    go underMeta tm =
      case tm of
        Var (Left M{}) -> mempty
        Var a ->
          if underMeta
          then mempty
          else Set.singleton a
        Bound{} -> mempty
        Ann a b -> go False a <> go False b
        Type -> mempty
        Pi a b -> goTele a <> go False b
        Lam _ a -> go False a
        App{} ->
          let
            (f, xs) = unfoldApps tm
          in
            case f of
              Var (Left M{}) -> foldMap (go True) xs
              Var a -> Set.singleton a <> foldMap (go False) xs
        Sigma _ a b -> go False a <> go False b
        Pair a b -> go False a <> go False b
        Fst a -> go False a
        Snd a -> go False a