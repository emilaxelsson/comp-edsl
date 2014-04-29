{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module General where



import qualified Data.Set as Set

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

prop_allVars = forAll genOpen $ \(t :: Term TestSig) -> Set.isSubsetOf (freeVars t) (allVars t)

