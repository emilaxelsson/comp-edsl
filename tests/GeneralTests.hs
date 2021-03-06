{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

import Control.Monad
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Language.Embedded
import Language.Embedded.Testing



prop_alphaEqRefl = forAll genClosed $ \(t :: Term TestSig) -> alphaEq t t

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
prop_renameUnique  = forAll genOpen $ \(t :: Term TestSig) -> alphaEq t (renameUnique t)
prop_renameUnique2 = forAll genOpen $ \(t :: Term TestSig) -> alphaEq (renameUnique t) t

-- Renaming does not change the free variables
prop_renameUniqueFree = forAll genOpen $ \(t :: Term TestSig) ->
    freeVars t == freeVars (renameUnique t)

-- Matching a substituted term against the original term yields the expected mapping
prop_subst =
    forAll genOpen $ \(t :: Term TestSig) ->
    let fv = Set.toList (freeVars t)
    in  not (null fv) ==>
          forAll genOpen $ \(new :: Term TestSig) ->
              ( forAll (oneof $ map return fv) $ \v ->
                  let t'      = subst v new t
                      Just ms = match t t'
                  in  and [(w==v && t==new) || (t == inject (Var w)) | (w,t) <- ms]
              )

-- Matching a substituted term against the original term yields the expected mapping
prop_parSubst =
    forAll genOpen $ \(t :: Term TestSig) ->
      let fv = Set.toList (freeVars t)
      in  not (null fv) ==>
            forAll (replicateM (length fv) genOpen) $ \(ss :: [Term TestSig]) ->
              let sub       = zip fv ss
                  t'        = parSubst sub t
                  Just sub' = match t t'
              in  Map.fromList sub == Map.fromList sub'

prop_matchRefl = forAll genClosed $ \(t :: Term TestSig) -> isJust (match t t)

prop_matchRename  = forAll genClosed $ \(t :: Term TestSig) -> isJust (match t (renameUnique t))
prop_matchRename2 = forAll genClosed $ \(t :: Term TestSig) -> isJust (match (renameUnique t) t)

prop_noMatch =
    forAll genClosed $ \t ->
      forAll (mutateTerm t) $ \tm -> isNothing (match t tm)

main = $defaultMainGenerator

