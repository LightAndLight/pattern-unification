module Main where

import Prelude hiding (pi)

import Test.Hspec

import Control.Monad.Except (runExcept)

import LambdaPi
import Supply (runSupplyT)

intSeed :: Int
intSeed = 1

intGen :: Int -> (Int, Int)
intGen a = (a, a+1)

runEta :: Equation Int -> Either (UnifyError Int) [Equation Int]
runEta = runExcept . runSupplyT intSeed intGen . eta

main :: IO ()
main = hspec $ do
  describe "eta expansion" $ do
    it "eta test 1" $ do
      let
        s1 = sigma (V 0, Type) Type
        ctx = [(0, Only s1)]
      runEta
        (Equation ctx
           (apply Fst (Var $ V 0)) Type
           (apply Fst (Var $ V 0)) Type)
        `shouldBe`
        Right [Equation ctx s1 Type s1 Type]
    it "eta test 2" $ do
      let
        x = Var $ V 0

        a = V 1
        ta = Var $ V 2
        b = Var $ V 3
        c = V 4
        tba = apply (Var a) b
        td = Var $ V 5
        p1 = pi (a, ta) [] $ pi (c, apply (Var a) b) [] td

        ctx = [(0, Only p1)]

        y1 = Var $ V 6
        y2 = Var $ V 7

        z1 = Var $ V 8
        z2 = Var $ V 9

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
        x = Var $ V 0

        a = V 1
        ta = Var $ V 2
        b = Var $ V 3
        c = V 4
        tba = apply (Var a) b
        td = Var $ V 5
        p1 = pi (a, ta) [(c, apply (Var a) b)] td

        ctx = [(0, Only p1)]

        y1 = Var $ V 6
        y2 = Var $ V 7

        z1 = Var $ V 8
        z2 = Var $ V 9

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
