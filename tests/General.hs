{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module General where



import Control.Monad
import Data.List
import qualified Data.Set as Set

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

import Language.Embedded
import Language.Embedded.Testing



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

prop_freeVars = forAll genClosed $ \(t :: Term TestSig) -> Set.null $ freeVars t

prop_usedVars = forAll genOpen $ \(t :: Term TestSig) -> Set.isSubsetOf (freeVars t) (usedVars t)
prop_allVars  = forAll genOpen $ \(t :: Term TestSig) -> Set.isSubsetOf (usedVars t) (allVars t)

-- Generate a finite sorted list of allocated variable names
genAllocs = fmap (sort . map Name) $ do
    n  <- choose (0,20)
    replicateM n $ choose (0,20)

-- Check that fresh variables are really fresh
prop_freshVars (NonNegative n) = forAll genAllocs $ \as -> notElem (freshVars as !! n) as

-- Check that the list of fresh variables is sorted
prop_freshVarsSorted = forAll genAllocs $ \as ->
    let fs = take 100 $ freshVars as
    in  fs == sort fs

-- Check that the list of fresh variables has no duplicates
prop_freshVarsUnique = forAll genAllocs $ \as ->
    let fs = take 100 $ freshVars as
    in  fs == nub fs

-- Check that fresh variables are not too big
prop_freshVarsSmall (NonNegative n) = forAll genAllocs $ \as ->
    (freshVars as !! n) <= (maximum (0:as) + fromIntegral n + 1)

