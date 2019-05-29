{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language KindSignatures #-}
{-# language LambdaCase #-}
{-# language RankNTypes #-}
{-# language TemplateHaskell #-}
{-# language QuantifiedConstraints #-}
module Pattern where

import Bound.Class (Bound(..))
import Bound.Scope (Scope, fromScope, toScope, abstract1, instantiate1, hoistScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Monad (ap)
import Control.Monad.Trans.Class (lift)
import Data.Coerce (Coercible, coerce)
import Data.Deriving (deriveEq1, deriveShow1, makeLiftEq)
import Data.Functor.Classes (Eq1(..), eq1, showsPrec1)
import Data.Functor.Product (Product)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set)
import Data.Text (Text)

import qualified Data.Set as Set

data Tele n f a
  = Done (f a)
  | Tele n (f a) (Tele n (Scope () f) a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

$(pure [])
instance (Eq n, Eq1 f, Monad f) => Eq1 (Tele n f) where
  liftEq = $(makeLiftEq ''Tele)

deriveShow1 ''Tele

instance Bound (Tele n) where
  Done a >>>= f = Done (a >>= f)
  Tele n s t >>>= f = Tele n (s >>= f) (t >>>= lift . f)

fromTele ::
  Monad f =>
  Tele n (Scope () f) a ->
  Tele n f (Var () a)
fromTele (Done a) = Done $ fromScope a
fromTele (Tele n a b) = Tele n (fromScope a) (fromTele b)

instTele ::
  Monad f =>
  f a ->
  Tele n (Scope () f) a ->
  Tele n f a
instTele = go id
  where
    go ::
      Monad f =>
      (forall a. f a -> g a) ->
      f a ->
      Tele n (Scope () f) a ->
      Tele n g a
    go f x (Done a) =
      Done $ f $ instantiate1 x a
    go f x (Tele n a b) =
      Tele n (f $ instantiate1 x a) (go (hoistScope f) (lift x) b)

abstractTele ::
  (Monad f, Eq a) =>
  [(a, f a)] ->
  f a ->
  Tele a f a
abstractTele [] a = Done a
abstractTele ((x, y) : as) a = Tele x y (go x $ abstractTele as a)
  where
    go :: (Monad f, Eq a) => a -> Tele a f a -> Tele a (Scope () f) a
    go a (Done b) = Done (abstract1 a b)
    go a (Tele b c d) = Tele b (abstract1 a c) (go a d)

data Tm a
  = Var a
  | Ann (Tm a) (Tm a)

  | Type

  | Pi Text (Tm a) (Tele Text (Scope () Tm) a)
  | Lam Text (Scope () Tm a)
  | App (Tm a) (Tm a)

  | Sigma Text (Tm a) (Scope () Tm a)
  | Pair (Tm a) (Tm a)
  | Fst (Tm a)
  | Snd (Tm a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Tm
deriveShow1 ''Tm
instance Eq a => Eq (Tm a) where; (==) = eq1
instance Show a => Show (Tm a) where; showsPrec = showsPrec1

instance Applicative Tm where; pure = return; (<*>) = ap
instance Monad Tm where
  return = Var
  tm >>= f =
    case tm of
      Var a -> f a
      Ann a b -> Ann (a >>= f) (b >>= f)

      Type -> Type

      Pi n a b -> Pi n (a >>= f) (b >>>= lift . f)
      Lam n a -> Lam n (a >>>= f)
      App a b -> App (a >>= f) (b >>= f)

      Sigma n a b -> Sigma n (a >>= f) (b >>>= f)
      Pair a b -> Pair (a >>= f) (a >>= f)
      Fst a -> Fst (a >>= f)
      Snd a -> Snd (a >>= f)

unfoldApps :: Tm a -> (Tm a, [Tm a])
unfoldApps = go []
  where
    go bs (App a b) = go (b : bs) a
    go bs a = (a, bs)

pi_ ::
  (Text, Ty Text) ->
  [(Text, Ty Text)] ->
  Ty Text ->
  Ty Text
pi_ a as b =
  case abstractTele (a : as) b of
    Done{} -> undefined
    Tele n s t -> Pi n s t

lam_ :: Text -> Tm Text -> Tm Text
lam_ n a = Lam n (abstract1 n a)

sigma_ :: (Text, Ty Text) -> Ty Text -> Ty Text
sigma_ (n, s) t = Sigma n s (abstract1 n t)

type Ty = Tm

data TypeError
  = NotInScope Text
  | ExpectedPi (Tm Text)
  | ExpectedSigma (Tm Text)
  | TypeIsTypeNot (Tm Text)
  | PiIsTypeNot (Tm Text)
  | LamIsPiNot (Tm Text)
  | SigmaIsTypeNot (Tm Text)
  | PairIsSigmaNot (Tm Text)
  | Can'tInfer (Tm Text)
  | TypeMismatch (Tm Text) (Tm Text)
  deriving (Eq, Show)

check ::
  Eq a =>
  (a -> Text) ->
  (a -> Maybe (Ty a)) ->
  Tm a ->
  Ty a ->
  Either TypeError ()
check names ctx tm ty =
  case tm of
    Type ->
      case ty of
        Type -> pure ()
        _ -> Left $ TypeIsTypeNot (names <$> ty)

    Pi n s t ->
      case ty of
        Type -> do
          () <- check names ctx s Type
          check
            (unvar (const n) names)
            (fmap (F <$>) . unvar (const $ Just s) ctx)
            (case fromTele t of
               Done tt -> tt
               Tele n tt rest -> Pi n tt rest)
            Type
        _ -> Left $ PiIsTypeNot (names <$> ty)

    Lam _ e ->
      case ty of
        Pi n s t ->
          check
            (unvar (const n) names)
            (unvar (const $ Just $ F <$> s) (fmap (F <$>) . ctx))
            (fromScope e)
            (case fromTele t of
               Done tt -> tt
               Tele n tt rest -> Pi n tt rest)
        _ -> Left $ LamIsPiNot (names <$> ty)

    Sigma n s t ->
      case ty of
        Type -> do
          () <- check names ctx s Type
          check
            (unvar (const n) names)
            (unvar (const $ Just $ F <$> s) (fmap (F <$>) . ctx))
            (fromScope t)
            Type
        _ -> Left $ SigmaIsTypeNot (names <$> ty)

    Pair a b ->
      case ty of
        Sigma _ s t -> do
          () <- check names ctx a s
          check names ctx b (instantiate1 a t)
        _ -> Left $ PairIsSigmaNot (names <$> ty)

    _ -> do
      ty' <- infer names ctx tm
      if ty == ty'
        then pure ()
        else Left $ TypeMismatch (names <$> ty) (names <$> ty')

infer ::
  Eq a =>
  (a -> Text) ->
  (a -> Maybe (Ty a)) ->
  Tm a ->
  Either TypeError (Tm a)
infer names ctx tm =
  case tm of
    Var a ->
      case ctx a of
        Nothing -> Left $ NotInScope (names a)
        Just ty -> pure ty

    App f x -> do
      fTy <- infer names ctx f
      case fTy of
        Pi _ s t -> do
          () <- check names ctx x s
          case instTele x t of
            Done tt -> pure tt
            Tele n tt rest -> pure $ Pi n tt rest
        _ -> Left $ ExpectedPi (names <$> fTy)

    Fst a -> do
      aTy <- infer names ctx a
      case aTy of
        Sigma _ x _ -> pure x
        _ -> Left $ ExpectedSigma (names <$> aTy)
    Snd a -> do
      aTy <- infer names ctx a
      case aTy of
        Sigma _ _ y -> pure $ instantiate1 (Fst a) y
        _ -> Left $ ExpectedSigma (names <$> aTy)

    Ann a t -> t <$ check names ctx a t
    _ -> Left $ Can'tInfer (names <$> tm)

data Equation f a =
  Equation
  { _eqTmL :: f a
  , _eqTyL :: f a
  , _eqTmR :: f a
  , _eqTyR :: f a
  }
  deriving (Eq, Show)

instance Bound Equation where
  Equation a b c d >>>= f = Equation (a >>= f) (b >>= f) (c >>= f) (d >>= f)

data Problem f a
  = ForallS (f a) (Problem f (Var () a))
  | ForallT (f a) (f a) (Problem f (Var Bool a))
  | Unify (Equation f a)

instance Bound Problem where
  ForallS a b >>>= f = ForallS (a >>= f) (b >>>= traverse f)
  ForallT a b c >>>= f = ForallT (a >>= f) (a >>= f) (c >>>= traverse f)
  Unify a >>>= f = Unify (a >>>= f)

data M a = M Int | N a
  deriving (Eq, Ord, Functor, Foldable, Traversable)
instance Applicative M where
  pure = N
  M a <*> _ = M a
  _ <*> M a = M a
  N f <*> N a = N (f a)
instance Monad M where
  M n >>= _ = M n
  N a >>= f = f a

newtype MT m a = MT { unMT :: m (M a) }
  deriving (Functor, Foldable, Traversable)
instance Applicative m => Applicative (MT m) where
  pure = MT . pure . pure
  MT f <*> MT a = MT $ (<*>) <$> f <*> a
instance Monad m => Monad (MT m) where
  MT a >>= f = MT $ do
    a' <- a
    case a' of
      M n -> pure $ M n
      N x | MT res <- f x -> res

fmv :: Tm (M a) -> Set Int
fmv = foldr (\case; M n -> Set.insert n; _ -> id) mempty

fv :: Ord a => Tm (M a) -> Set a
fv = foldl (foldr Set.insert) mempty

fv_rig :: Ord a => Tm (M a) -> Set (M a)
fv_rig = go False
  where
    go :: Ord a => Bool -> Tm (M a) -> Set (M a)
    go underMeta tm =
      case f of
        Var a -> (if underMeta then id else Set.insert a) $ foldMap (go True) xs
        Ann a b -> go False a <> go False b
        Type -> mempty
        Pi _ s t ->
          go False s <>
          filterVars
            (go False $
             case sequence <$> fromTele t of
               Done tt -> tt
               Tele n ss tt -> Pi n ss tt)
        Lam _ e ->
          filterVars $
          go False (sequence <$> fromScope e)
        Sigma _ s t -> go False s <> filterVars (go False (sequence <$> fromScope t))
        Pair a b -> go False a <> go False b
        Fst a -> go False a
        Snd a -> go False a
      where
        (f, xs) = unfoldApps tm

    filterVars :: Ord a => Set (M (Var () a)) -> Set (M a)
    filterVars =
      foldr
        (\case; M n -> Set.insert (M n); N (B ()) -> id; N (F a) -> Set.insert (N a))
        mempty
