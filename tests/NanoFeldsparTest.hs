{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

import Control.Monad
import Data.List

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.QuickCheck

import Data.ByteString.Lazy.UTF8 (fromString)

import Data.Comp.Generic

import Language.Embedded
import Language.Embedded.Testing
import qualified NanoFeldspar as Nano



scProd :: [Float] -> [Float] -> Float
scProd as bs = sum $ zipWith (*) as bs

prop_scProd as bs = scProd as bs == Nano.eval Nano.scProd as bs

genMat :: Gen [[Float]]
genMat = sized $ \s -> do
    x <- liftM succ $ choose (0, s `mod` 10)
    y <- liftM succ $ choose (0, s `mod` 10)
    replicateM y $ vector x

forEach = flip map

matMul :: [[Float]] -> [[Float]] -> [[Float]]
matMul a b = forEach a $ \a' ->
               forEach (transpose b) $ \b' ->
                 scProd a' b'

prop_matMul =
    forAll genMat $ \a ->
      forAll genMat $ \b ->
        matMul a b == Nano.eval Nano.matMul a b

mkGold_scProd = writeFile "tests/gold/scProd.txt" $ showAST Nano.scProd
mkGold_matMul = writeFile "tests/gold/matMul.txt" $ showAST Nano.matMul

alphaRename :: (Binding :<: f, Functor f) => Term f -> Term f
alphaRename = transform rename
  where
    rename t
        | Just (Var v)   <- project t = inject (Var (v+1))
        | Just (Lam v a) <- project t = inject (Lam (v+1) a)
        | otherwise = t

badRename :: (Binding :<: f, Functor f) => Term f -> Term f
badRename = transform rename
  where
    rename t
        | Just (Var v)   <- project t = inject (Var (v+1))
        | Just (Lam v a) <- project t = inject (Lam (v-1) a)
        | otherwise = t

checkAlphaEq a    = alphaEq a (alphaRename a)
checkAlphaEqBad a = not (alphaEq a (badRename a))

prop_alphaEq = forAll genClosed $ \(t :: Term TestSig) -> checkAlphaEq t

prop_notAlphaEq =
    forAll genClosed $ \t ->
      forAll (mutateTerm t) $ \tm -> not (alphaEq t tm)

tests = testGroup "TreeTests"
    [ goldenVsString "scProd tree" "tests/gold/scProd.txt" $ return $ fromString $ showAST Nano.scProd
    , goldenVsString "matMul tree" "tests/gold/matMul.txt" $ return $ fromString $ showAST Nano.matMul

    , testProperty "scProd eval" prop_scProd
    , testProperty "matMul eval" prop_matMul

    , testProperty "alphaEq"               prop_alphaEq
    , testProperty "notAlphaEq"            prop_notAlphaEq
    , testProperty "alphaEq scProd"        (checkAlphaEq (desugar' Nano.scProd))
    , testProperty "alphaEq matMul"        (checkAlphaEq (desugar' Nano.matMul))
    , testProperty "alphaEq scProd matMul" (not (alphaEq (desugar' Nano.scProd) (desugar' Nano.matMul)))
    , testProperty "alphaEqBad scProd"     (checkAlphaEqBad (desugar' Nano.scProd))
    , testProperty "alphaEqBad matMul"     (checkAlphaEqBad (desugar' Nano.matMul))
    ]

main = defaultMain tests

