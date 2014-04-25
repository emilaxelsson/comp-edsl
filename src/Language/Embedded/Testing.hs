module Language.Embedded.Testing where



import Control.Monad
import Test.QuickCheck

import Data.Comp.Render

import Language.Embedded

import Debug.Trace



----------------------------------------------------------------------------------------------------
-- * Generation of untyped lambda terms
----------------------------------------------------------------------------------------------------

type TestSig = Construct :+: Binding

-- | Generate a variable name
genName :: Gen Name
genName = do
    Positive v <- arbitrary
    return (Name v)

-- | Generate a bound (probability b/(b+f)) or free (probability f/(b+f)) variable
pickVar :: Int -> Int -> [Name] -> Gen Name
pickVar _ 0 [] = error "pickVar: no variables in scope"
pickVar _ _ [] = genName
pickVar b f env = frequency
    [ (b, oneof $ map return env)
    , (f, genName)
    ]

-- | Generate a random constructor
genConstr :: Int -> Gen (Term TestSig) -> Gen (TestSig (Term TestSig))
genConstr c term = fmap (inj . Construct ("constr" ++ show c)) $ replicateM c term

genTerm
    :: Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> Gen (Term TestSig)
genTerm _ 0 env = fmap Term $ genConstr 0 undefined
genTerm closed s env = frequency
    [ (1, do
            c <- choose (0,3)
            fmap Term $ genConstr c (genTerm closed (s `mod` c) env))
    , (freqVar, do
            v <- pickVar 5 freqFree env
            return $ inject $ Var v
      )
    , (1, do
            v <- pickVar 1 2 env
            fmap (inject . Lam v) $ genTerm closed (s-1) (v:env)
      )
    ]
  where
    freqVar  = if closed && null env then 0 else 1
    freqFree = if closed || null env then 0 else 1

-- | Generate a possibly open term with many binders and high probability of shadowing
genClosed :: Gen (Term TestSig)
genClosed = sized $ \s -> genTerm True s []

-- | Generate a possibly open term with many binders and high probability of shadowing
genOpen :: Gen (Term TestSig)
genOpen = sized $ \s -> genTerm False s []

mutateName :: Name -> Gen Name
mutateName (Name v) = fmap (Name . (v+) . getPositive) arbitrary

oneHot :: Int -> Gen [Bool]
oneHot l = do
    n <- choose (0,l-1)
    return $ replicate n False ++ [True] ++ replicate (l-n-1) False

-- | Mutates a term to get another one that is guaranteed not to be alpha-equivalent
mutateTerm :: Term TestSig -> Gen (Term TestSig)
mutateTerm t
    | Just (Var v) <- project t = fmap (inject . Var) $ mutateName v
mutateTerm t
    | Just (Lam v a) <- project t = fmap (inject . Lam v) $ mutateTerm a
mutateTerm t
    | Just (Construct c []) <- project t = return $ inject $ Construct (c++c) []
    | Just (Construct c as) <- project t = frequency
        [ (1, return $ inject (Construct (c++c) as))
        , (15, do
                mask <- oneHot (length as)
                as'  <- sequence [if hot then mutateTerm a else return a | (a,hot) <- zip as mask]
                return $ inject $ Construct c as'
          )
        ]

