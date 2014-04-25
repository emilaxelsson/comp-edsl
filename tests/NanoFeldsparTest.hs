import Control.Monad
import Data.List

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.QuickCheck

import Data.ByteString.Lazy.UTF8 (fromString)

import Data.Comp.Generic

import Language.Embedded.Syntax
import Language.Embedded.Constructs
import Language.Embedded.Algorithms
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

alphaRename :: Term Nano.FeldF -> Term Nano.FeldF
alphaRename = transform rename
  where
    rename t
        | Just (Var v)   <- project t = inject (Var (v+1))
        | Just (Lam v a) <- project t = inject (Lam (v+1) a)
        | otherwise = t

badRename :: Term Nano.FeldF -> Term Nano.FeldF
badRename = transform rename
  where
    rename t
        | Just (Var v)   <- project t = inject (Var (v+1))
        | Just (Lam v a) <- project t = inject (Lam (v-1) a)
        | otherwise = t

prop_alphaEq a = alphaEq a (alphaRename a)

prop_alphaEqBad a = alphaEq a (badRename a)

tests = testGroup "TreeTests"
    [ goldenVsString "scProd tree" "tests/gold/scProd.txt" $ return $ fromString $ showAST Nano.scProd
    , goldenVsString "matMul tree" "tests/gold/matMul.txt" $ return $ fromString $ showAST Nano.matMul
    , testProperty "scProd eval" prop_scProd
    , testProperty "matMul eval" prop_matMul
    , testProperty "alphaEq scProd"        (prop_alphaEq (desugar' Nano.scProd))
    , testProperty "alphaEq matMul"        (prop_alphaEq (desugar' Nano.matMul))
    , testProperty "alphaEq scProd matMul" (not (alphaEq (desugar' Nano.scProd) (desugar' Nano.matMul)))
    , testProperty "alphaEqBad scProd"     (not (prop_alphaEqBad (desugar' Nano.scProd)))
    , testProperty "alphaEqBad matMul"     (not (prop_alphaEqBad (desugar' Nano.matMul)))
    ]

main = defaultMain tests

