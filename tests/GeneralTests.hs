{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

import Control.Monad
import qualified Data.Foldable as Foldable
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Language.Embedded
import Language.Embedded.Sharing
import Language.Embedded.Testing



prop_rename1 w (Open t) = t == rename w w t

prop_rename2 v w (Open t) =
    not (v `Set.member` freeVars t) ==>
      t == rename v w t

prop_rename3 v w (Open t) =
    (v `Set.member` freeVars t) && v/=w ==>
      t /= rename v w t

prop_rename4 v w (Open t) =
    not (w `Set.member` allVars t) ==>
      t == rename w v (rename v w t)

prop_alphaEqRefl (Open t) = alphaEq t t

prop_alphaEqSymm (Open t) =
    let left  = alphaEq t (shiftVars t)
        right = alphaEq (shiftVars t) t
    in  collect left (left == right)

prop_notAlphaEq (Open t) = forAll (mutateTerm t) $ \tm -> not (alphaEq t tm)

-- Check alphaEq for terms that are almost equivalent, but where one has shadowing
prop_alphaEqShadow = not (alphaEq t1 t2) && not (alphaEq t2 t1)
  where
    t1 :: Term (Binding :+: Construct)
    t1 = mkLam 0 $ mkc2 (mkLam 1 $ mkVar 1) (mkLam 4 $ mkLam 3 $ mkLam 5 $ mkVar 4)
    t2 = mkLam 0 $ mkc2 (mkLam 1 $ mkVar 1) (mkLam 2 $ mkLam 3 $ mkLam 2 $ mkVar 2)

prop_freeVars (Closed t) = Set.null $ freeVars t

prop_usedVars (Open t) = Set.isSubsetOf (freeVars t) (usedVars t)
prop_allVars  (Open t) = Set.isSubsetOf (usedVars t) (allVars t)

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
prop_renameUnique  (Open t) = alphaEq t (renameUnique t)
prop_renameUnique2 (Open t) = alphaEq (renameUnique t) t

-- Renaming does not change the free variables
prop_renameUniqueFree (Open t) = freeVars t == freeVars (renameUnique t)

-- Matching a substituted term against the original term yields the expected mapping
prop_subst (Open t) (Open new) =
    not (null fv) ==>
        forAll (oneof $ map return fv) $ \v ->
          let t'      = subst v new t
              Just ms = match t t'
          in  and [(w==v && t==new) || (t == inject (Var w)) | (w,t) <- ms]

  where
    fv = Set.toList (freeVars t)

-- Matching a substituted term against the original term yields the expected mapping
prop_parSubst (Open t) =
    not (null fv) ==>
        forAll (fmap (map unOpen) $ replicateM (length fv) arbitrary) $ \ss ->
          let sub       = fromListEnv $ zip fv ss
              t'        = parSubst sub t
              Just sub' = match t t'
          in  sub == Map.fromList sub'
  where
    fv = Set.toList (freeVars t)

prop_matchRefl (Open t) = isJust (match t t)

prop_matchRename1 (Open t) = isJust (match t (renameUnique t))
prop_matchRename2 (Open t) = isJust (match (renameUnique t) t)

prop_noMatch (Closed t) = forAll (mutateTerm t) $ \tm -> isNothing (match t tm)

prop_ClosedDAG1 (ClosedDAG t)  = Set.null $ freeVars t
prop_ClosedDAG2 (ClosedDAG t)  = Set.null $ freeDVars t
prop_OpenDAG    (OpenDAG t)    = Set.null $ freeDVars t
prop_DAGEnv     (DAGEnv env t) = Set.null $ freeDVars $ addDefs env t

-- 'foldDAG' has the same behavior as 'cata' composed with 'inlineLet'
prop_foldDAG (OpenDAG t) = foldDAG alg t == cata alg (inlineDAG t)
  where
    alg f = succ $ sum $ zipWith (*) (cycle [1,-3]) (Foldable.toList f)

prop_inlineDAG (OpenDAG t) = inlineDAG t `alphaEq` reference t
  where
    reference = foldDAG Term . renameUnique
      -- `foldDAG Term` is a correct inliner if names are unique

prop_splitDefs_removes_lets (OpenDAGTop t) =
    case unTerm $ snd $ splitDefs t of
        Inl (DLet _ _ _) -> False
        _ -> True

prop_splitDefs_addDefs (OpenDAGTop t) = uncurry addDefs (splitDefs t) == t

-- | 'expose' does not change the call-by-name semantics
prop_expose (DAGEnv env t) =
    (inlineDAG (addDefs env $ Term $ Inr $ expose (Set.toList $ allVars (addDefs env t)) env t) `alphaEq` inlineDAG (addDefs env t))

-- Test a single property
qc = defaultMain . testProperty "single test"

-- Run n tests
qcN n = defaultMain . localOption (n :: QuickCheckTests) . testProperty "single test"

-- Test with a specific seed
-- (e.g. "89 TFGenR F6F9D6562721E71F7FC871776E0A9072E97E1E864F914DC45FE351F5BB373BAF 0 1125899906842623 50 0")
qcSeed seed = defaultMain . localOption opt . testProperty "single test"
  where
    Just opt = parseValue seed :: Maybe QuickCheckReplay

main = $defaultMainGenerator

