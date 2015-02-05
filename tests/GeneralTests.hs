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



prop_rename1 w =
    forAll genOpen $ \(t :: Term TestSig) ->
      t == rename w w t

prop_rename2 v w =
    forAll genOpen $ \(t :: Term TestSig) ->
      not (v `Set.member` freeVars t) ==>
        t == rename v w t

prop_rename3 v w =
    forAll genOpen $ \(t :: Term TestSig) ->
      (v `Set.member` freeVars t) && v/=w ==>
        t /= rename v w t

prop_rename4 v w =
    forAll genOpen $ \(t :: Term TestSig) ->
      not (w `Set.member` allVars t) ==>
        t == rename w v (rename v w t)

prop_alphaEqRefl = forAll genOpen $ \(t :: Term TestSig) -> alphaEq t t

prop_alphaEqSymm  = forAll genOpen $ \(t :: Term TestSig) ->
    let left  = alphaEq t (shiftVars t)
        right = alphaEq (shiftVars t) t
    in  collect left (left == right)

prop_notAlphaEq =
    forAll genOpen $ \t ->
      forAll (mutateTerm t) $ \tm -> not (alphaEq t tm)

-- Check alphaEq for terms that are almost equivalent, but where one has shadowing
prop_alphaEqShadow = not (alphaEq t1 t2) && not (alphaEq t2 t1)
  where
    t1 :: Term TestSig
    t1 = mkLam 0 $ mkc2 (mkLam 1 $ mkVar 1) (mkLam 4 $ mkLam 3 $ mkLam 5 $ mkVar 4)
    t2 = mkLam 0 $ mkc2 (mkLam 1 $ mkVar 1) (mkLam 2 $ mkLam 3 $ mkLam 2 $ mkVar 2)

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
              let sub       = fromListEnv $ zip fv ss
                  t'        = parSubst sub t
                  Just sub' = match t t'
              in  sub == Map.fromList sub'

prop_matchRefl = forAll genOpen $ \(t :: Term TestSig) -> isJust (match t t)

prop_matchRename  = forAll genOpen $ \(t :: Term TestSig) -> isJust (match t (renameUnique t))
prop_matchRename2 = forAll genOpen $ \(t :: Term TestSig) -> isJust (match (renameUnique t) t)

prop_noMatch =
    forAll genClosed $ \t ->
      forAll (mutateTerm t) $ \tm -> isNothing (match t tm)

-- 'foldDAG' has the same behavior as 'cata' composed with 'inlineLet'
prop_foldDAG = forAll genOpenDAG $ \(t :: DAG (Binding :+: Construct)) ->
    foldDAG alg t == cata alg (inlineDAG t)
  where
    alg f = succ $ sum $ zipWith (*) (cycle [1,-3]) (Foldable.toList f)

prop_inlineDAG = forAll genOpenDAG $ \(t :: DAG (Binding :+: Construct)) ->
    inlineDAG t `alphaEq` reference t
  where
    reference = foldDAG Term . renameUnique
      -- `foldDAG Term` is a correct inliner if names are unique

prop_splitDefs_removes_lets =
    forAll genOpenDAGTop $ \(t :: DAG (Binding :+: Construct)) ->
      case unTerm $ snd $ splitDefs t of
          Inl (DLet _ _ _) -> False
          _ -> True

prop_splitDefs_addDefs =
    forAll genOpenDAGTop $ \(t :: DAG (Binding :+: Construct)) ->
      uncurry addDefs (splitDefs t) == t

-- | 'expose' does not change the call-by-name semantics
prop_expose =
    forAll genDAGEnv $ \(env, t :: DAG (Binding :+: Construct)) ->
      uniqueDefs env ==>  -- TODO This requirement rules out long environments
        (inlineDAG (addDefs env $ Term $ Inr $ expose (Set.toList $ allVars (addDefs env t)) env t) `alphaEq` inlineDAG (addDefs env t))
  where
    uniqueDefs ds = vs == nub vs
      where
        vs = map fst ds

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

