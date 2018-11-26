{-# language OverloadedLists #-}
module Main where

import Prelude hiding (pi)

import Test.Hspec

import Control.Lens.Review ((#))
import Control.Monad.Except (runExcept)
import Control.Monad.State (runStateT)
import Control.Monad.Trans (lift)
import Data.Functor.Identity (Identity(..))

import Equation
import LambdaPi
import Solver
import Solver.Class
import Supply
import Unification

intSeed :: Int
intSeed = 1

intGen :: Int -> (Int, Int)
intGen a = (a, a+1)

runEta
  :: Equation Meta Int
  -> Either (UnifyError Meta Int) [Equation Meta Int]
runEta = runExcept . runSupplyT intSeed intGen . eta

runFlexRigid
  :: MetaContext v
  -> SupplyT Int Int (SolverT v (SolverError v) Identity) a
  -> Either (SolverError v) (a, MetaContext v)
runFlexRigid ctx =
  runExcept .
  flip runStateT ctx .
  unSolverT .
  runSupplyT intSeed intGen

main :: IO ()
main = hspec $ do
  describe "type checker" $ do
    it "(\\x. y. y) : pi (t : Type). pi (a : t). a" $ do
      check
        (const Nothing)
        (Lam $ lift $ lam "x" $ Var "x")
        (pi ("t", Type) $ pi ("a", Var "t") $ Var "a") `shouldBe`
        True
  describe "flex-rigid" $ do
    it "flex-rigid test 1" $ do
      let
        a :: Int
        a = 0

        t :: Tm (Meta Int)
        t = Var $ _V # 1

        x = 2

        p :: Problem Int
        p =
          Problem [] $
          Equation
            -- x : t
            [(x, Only t)]
            -- a x : t
            (Neutral (Var $ _M # a) [Var (_V # x)]) t
            -- x : t
            (Var $ _V # x) t


        expectedMC =
          MetaContext
            [MetaDecl a $ pi (_V # 3, t) t]
            Nothing
            []
            [(a, lam (_V # 0) (Var $ _V # 0))]

      runFlexRigid
        (MetaContext
           -- a : (c : t) -> t
           [MetaDecl a $ pi (_V # 3, t) t]
           (Just $ p)
           []
           [])
        flexRigid
        `shouldBe` Right ((), expectedMC)
  describe "eta expansion" $ do
    it "eta test 1" $ do
      let
        s1 = sigma (_V # 0, Type) Type
        ctx = [(0, Only s1)]
      runEta
        (Equation ctx
           (apply Fst (Var $ _V # 0)) Type
           (apply Fst (Var $ _V # 0)) Type)
        `shouldBe`
        Right [Equation ctx s1 Type s1 Type]
    it "eta test 2" $ do
      let
        x = Var $ _V # 0

        a = _V # 1
        ta = Var $ _V # 2
        b = Var $ _V # 3
        c = _V # 4
        td = Var $ _V # 5
        p1 = pi (a, ta) $ pi (c, apply (Var a) b) td

        ctx = [(0, Only p1)]

        y1 = Var $ _V # 6
        y2 = Var $ _V # 7

        z1 = Var $ _V # 8
        z2 = Var $ _V # 9

      runEta
        (Equation ctx
           (apply z1 $ apply y1 x) Type
           (apply z2 $ apply y2 x) Type)
        `shouldBe`
        Right
          [ Equation ctx p1 Type p1 Type
          , Equation ctx y1 ta y2 ta
          , Equation ctx z1 (apply y1 b) z2 (apply y2 b)
          ]
    it "eta test 3" $ do
      let
        x = Var $ _V # 0

        a = _V # 1
        ta = Var $ _V # 2
        b = Var $ _V # 3
        c = _V # 4
        td = Var $ _V # 5
        p1 = pi (a, ta) $ pi (c, apply (Var a) b) td

        ctx = [(0, Only p1)]

        y1 = Var $ _V # 6
        y2 = Var $ _V # 7

        z1 = Var $ _V # 8
        z2 = Var $ _V # 9

      runEta
        (Equation ctx
           (apply z1 $ apply y1 x) Type
           (apply z2 $ apply y2 x) Type)
        `shouldBe`
        Right
          [ Equation ctx p1 Type p1 Type
          , Equation ctx y1 ta y2 ta
          , Equation ctx z1 (apply y1 b) z2 (apply y2 b)
          ]
