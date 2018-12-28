{-# language OverloadedLists #-}
module Main where

import Prelude hiding (pi)

import Data.Coerce (coerce)
import Test.Hspec

import LambdaPi
import Supply
import Unification

nameSeed :: Int
nameSeed = 0

nameGen :: Int -> (String, Int)
nameGen n = ("t" <> show n, n+1)

main :: IO ()
main = hspec $ do
  describe "solve1 tests" $ do
    it "α x =?= x   -   α := λ. 0" $ do
      runSupply nameSeed nameGen
        (solve1 (coerce $ Var (M "alpha") .@ Var (N "x")) (pure "x"))
        `shouldBe`
        Success [Solution "alpha" $ lamM "x" $ pure "x"] []
    it "α x y =?= x   -   α := λ. λ. 1" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x") .@ Var (N "y"))
           (coerce $ Var (N "x")))
        `shouldBe`
        Success [Solution "alpha" $ lamM "x" $ lamM "y" $ pure "x"] []
    it "α x y =?= y   -   α := λ. λ. 0" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x") .@ Var (N "y"))
           (coerce $ Var (N "y")))
        `shouldBe`
        Success [Solution "alpha" $ lamM "x" $ lamM "y" $ pure "y"] []
    it "α x y =?= α y   -   fails" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x") .@ Var (N "y"))
           (coerce $ Var (M "alpha") .@ Var (N "y")))
        `shouldBe`
        Failure
    it "α x y =?= α x z   -   α := λ. λ. β 1   ,   β x =?= β x" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x") .@ Var (N "y"))
           (coerce $ Var (M "alpha") .@ Var (N "x") .@ Var (N "z")))
        `shouldBe`
        Success
          [ Solution "alpha" $
            lamM "x" $ lamM "_" . coerce $ Var (M "t0") .@ Var (N "x")
          ]
          [coerce (Var (M "t0") .@ Var (N "x"), Var (M "t0") .@ Var (N "x"))]
    it "α x x =?= α y x   -   α := λ. λ. β 0   ,   β x =?= β x" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x") .@ Var (N "x"))
           (coerce $ Var (M "alpha") .@ Var (N "y") .@ Var (N "x")))
        `shouldBe`
        Success
          [ Solution "alpha" $
            lamM "y" $ lamM "x" . coerce $ Var (M "t0") .@ Var (N "x")
          ]
          [coerce (Var (M "t0") .@ Var (N "x"), Var (M "t0") .@ Var (N "x"))]
    it "α x =?= x (β y)   -   β := λ. γ   ,   α x =?= x γ" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x"))
           (coerce $ Var (N "x") .@ (Var (M "beta") .@ Var (N "y"))))
        `shouldBe`
        Success
          [Solution "beta" $ lamM "y" . coerce $ Var (M "t0")]
          [coerce (Var (M "alpha") .@ Var (N "x"), Var (N "x") .@ Var (M "t0"))]
    it "α x =?= x γ   -   α := λ. 0 γ" $ do
      runSupply nameSeed nameGen
        (solve1
           (coerce $ Var (M "alpha") .@ Var (N "x"))
           (coerce $ Var (N "x") .@ Var (M "gamma")))
        `shouldBe`
        Success
          [Solution "alpha" $ lamM "x" . coerce $ Var (N "x") .@ Var (M "gamma")]
          []
    it "λ. 0 =?= λ. α 0   -   <x =?= α >x" $ do
      runSupply nameSeed nameGen
        (solve1
           (lamM "x" $ pure "x")
           (lamM "x" . coerce $ Var (M "alpha") .@ Var (N "x")))
        `shouldBe`
        Success
          []
          [coerce (Var $ L "t0", Var (M "alpha") .@ Var (R "t0"))]
    it "<x =?= α >x   -   α := λ. 0" $ do
      runSupply nameSeed nameGen
        (solve1
           (MetaT $ Var $ L "t0")
           (MetaT $ Var (M "alpha") .@ Var (R "t0")))
        `shouldBe`
        Success
          [Solution "alpha" $ lamM "x" (pure "x")]
          []
