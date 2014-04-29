{-# LANGUAGE ScopedTypeVariables #-}

module General where



import Control.Monad
import Data.List
import qualified Data.Set as Set

import Test.Tasty.QuickCheck

import Language.Embedded
import Language.Embedded.Testing



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

-- Check that there are no gaps or duplicates in the list of fresh variables
prop_freshVarsCompact = forAll (fmap nub genAllocs) $ \as ->
    sort (take 100 (as ++ freshVars as)) == [0..99]

-- A term is alpha-equivalent to its unique renaming
prop_renameUnique = forAll genOpen $ \(t :: Term TestSig) -> alphaEq t (renameUnique t)

-- Renaming does not change the free variables
prop_renameUniqueFree = forAll genOpen $ \(t :: Term TestSig) ->
    freeVars t == freeVars (renameUnique t)

