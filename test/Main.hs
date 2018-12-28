{-# language OverloadedLists #-}
module Main where

import Prelude hiding (pi)

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
      runSupply nameSeed nameGen (solve1 (Var (M "alpha") .@ Var (N "x")) (Var (N "x")))
        `shouldBe`
        Success [Solution "alpha" $ lam (N "x") (Var $ N "x")] []
    it "α x y =?= x   -   α := λ. λ. 1" $ do
      runSupply nameSeed nameGen (solve1 (Var (M "alpha") .@ Var (N "x") .@ Var (N "y")) (Var (N "x")))
        `shouldBe`
        Success [Solution "alpha" $ lam (N "x") $ lam (N "y") $ (Var $ N "x")] []
    it "α x y =?= y   -   α := λ. λ. 0" $ do
      runSupply nameSeed nameGen (solve1 (Var (M "alpha") .@ Var (N "x") .@ Var (N "y")) (Var (N "y")))
        `shouldBe`
        Success [Solution "alpha" $ lam (N "x") $ lam (N "y") $ (Var $ N "y")] []
    it "α x y =?= α y   -   fails" $ do
      runSupply nameSeed nameGen (solve1 (Var (M "alpha") .@ Var (N "x") .@ Var (N "y")) (Var (M "alpha") .@ Var (N "y")))
        `shouldBe`
        Failure
    it "α x y =?= α x z   -   α := λ. λ. β 1   ,   β x =?= β x" $ do
      runSupply nameSeed nameGen (solve1 (Var (M "alpha") .@ Var (N "x") .@ Var (N "y")) (Var (M "alpha") .@ Var (N "x") .@ Var (N "z")))
        `shouldBe`
        Success
          [ Solution "alpha" $
            lam (N "x") $ lam (N "_") $ Var (M "t0") .@ Var (N "x")
          ]
          [(Var (M "t0") .@ Var (N "x"), Var (M "t0") .@ Var (N "x"))]
    it "α x x =?= α y x   -   α := λ. λ. β 0   ,   β x =?= β x" $ do
      runSupply nameSeed nameGen
        (solve1
           (Var (M "alpha") .@ Var (N "x") .@ Var (N "x"))
           (Var (M "alpha") .@ Var (N "y") .@ Var (N "x")))
        `shouldBe`
        Success
          [ Solution "alpha" $
            lam (N "y") $ lam (N "x") $ Var (M "t0") .@ Var (N "x")
          ]
          [(Var (M "t0") .@ Var (N "x"), Var (M "t0") .@ Var (N "x"))]
    it "α x =?= x (β y)   -   β := λ. γ   ,   α x =?= x γ" $ do
      runSupply nameSeed nameGen
        (solve1
           (Var (M "alpha") .@ Var (N "x"))
           (Var (N "x") .@ (Var (M "beta") .@ Var (N "y"))))
        `shouldBe`
        Success
          [Solution "beta" $ lam (N "y") $ Var (M "t0")]
          [(Var (M "alpha") .@ Var (N "x"), Var (N "x") .@ Var (M "t0"))]
    it "α x =?= x γ   -   α := λ. 0 γ" $ do
      runSupply nameSeed nameGen
        (solve1
           (Var (M "alpha") .@ Var (N "x"))
           (Var (N "x") .@ Var (M "gamma")))
        `shouldBe`
        Success
          [Solution "alpha" $ lam (N "x") $ Var (N "x") .@ Var (M "gamma")]
          []
    it "λ. 0 =?= λ. α 0   -   <x =?= α >x" $ do
      runSupply nameSeed nameGen
        (solve1
           (lam (N "x") $ Var (N "x"))
           (lam (N "x") $ Var (M "alpha") .@ Var (N "x")))
        `shouldBe`
        Success
          []
          [(Var $ L "t0", Var (M "alpha") .@ Var (R "t0"))]
    it "<x =?= α >x   -   α := λ. 0" $ do
      runSupply nameSeed nameGen
        (solve1
           (Var $ L "t0")
           (Var (M "alpha") .@ Var (R "t0")))
        `shouldBe`
        Success
          [Solution "alpha" $ lam (N "x") (Var $ N "x")]
          []
