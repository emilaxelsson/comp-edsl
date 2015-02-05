{-# LANGUAGE NoMonomorphismRestriction #-}

module Language.Embedded.Testing where



import Control.Monad
import Data.Foldable (toList)
import Data.Traversable (traverse)
import Test.QuickCheck

import Data.Comp.Ops

import Language.Embedded
import Language.Embedded.Sharing



----------------------------------------------------------------------------------------------------
-- Debugging API
----------------------------------------------------------------------------------------------------

var_       = inject . Var
lam_ v     = inject . Lam v
c0         = inject $ Construct "c0" []
c1 a       = inject $ Construct "c1" [a]
c2 a b     = inject $ Construct "c2" [a,b]
c3 a b c   = inject $ Construct "c3" [a,b,c]

ddvar_      = Term . Inr . DVar
dlet_ v a b = Term $ Inr $ DLet v a b
dvar_       = Term . Inl . inj . Var
dlam_ v     = Term . Inl . inj . Lam v
d0          = Term $ Inl $ inj $ Construct "d0" []
d1 a        = Term $ Inl $ inj $ Construct "d1" [a]
d2 a b      = Term $ Inl $ inj $ Construct "d2" [a,b]
d3 a b c    = Term $ Inl $ inj $ Construct "d3" [a,b,c]



----------------------------------------------------------------------------------------------------
-- * Generation of untyped lambda terms
----------------------------------------------------------------------------------------------------

class Constructors f
  where
    constructors :: [f ()]

instance (Constructors f, Constructors g) => Constructors (f :+: g)
  where
    constructors = map Inl constructors ++ map Inr constructors

instance Constructors Construct
  where
    constructors = [Construct ("constr" ++ show c) $ replicate c () | c <- [0..3]]

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

genTerm
    :: (Constructors f, Traversable f)
    => Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> Gen (Term (Binding :+: f))
genTerm closed 0 env = frequency
    [ (1, fmap Term
        $ oneof
        $ map (return . Inr . fmap (const undefined))
        $ filter (null . toList) constructors
      )
    , (freqVar, do
            v <- pickVar 5 freqFree env
            return $ Term $ Inl $ Var v
      )
    ]
  where
    freqVar  = if closed && null env then 0 else 4
    freqFree = if closed then 0 else 1
genTerm closed s env = frequency
    [ (6, do
            c <- oneof $ map (return . Inr) $ filter (not . null . toList) constructors
            let l = length (toList c)
            fmap Term $ traverse (\_ -> genTerm closed (s `div` l) env) c
      )
    , (6, do
            v <- pickVar 1 3 env
            fmap (Term . Inl . Lam v) $ genTerm closed (s-1) (v:env)
      )
    , (1, genTerm closed 0 env)
    ]

-- | Generate a possibly open term with many binders and high probability of shadowing
genClosed :: (Constructors f, Functor f, Traversable f) => Gen (Term (Binding :+: f))
genClosed = sized $ \s -> genTerm True (20*s) []

-- | Generate a possibly open term with many binders and high probability of shadowing
genOpen :: (Constructors f, Functor f, Traversable f) => Gen (Term (Binding :+: f))
genOpen = sized $ \s -> genTerm False (20*s) []

-- TODO Implement shrinking

mutateName :: Name -> Gen Name
mutateName (Name v) = fmap (Name . (v+) . getPositive) arbitrary

oneHot :: Int -> Gen [Bool]
oneHot l = do
    n <- choose (0,l-1)
    return $ replicate n False ++ [True] ++ replicate (l-n-1) False

-- | Adds 1 to all bound variables to give a different term that is quite probable to be alpha
-- equivalent to the first and quite probable to be alpha-inequivalent due to capturing of free
-- variables
shiftVars :: (Binding :<: f, Functor f) => Term f -> Term f
shiftVars = go []
  where
    go env t@(Term f)
      | Just (Var v) <- project t = case lookup v env of
          Just v' -> inject $ Var v'
          _       -> t
      | Just (Lam v a) <- project t = inject $ Lam (v+1) $ go ((v,v+1):env) a
      | otherwise = Term $ fmap (go env) f

type TestSig = Binding :+: Construct

-- | Mutates a term to get another one that is guaranteed not to be alpha-equivalent
mutateTerm :: Term TestSig -> Gen (Term TestSig)
mutateTerm t
    | Just (Var v)          <- project t = fmap (inject . Var) $ mutateName v
    | Just (Lam v a)        <- project t = fmap (inject . Lam v) $ mutateTerm a
    | Just (Construct c []) <- project t = return $ inject $ Construct (c++c) []
    | Just (Construct c as) <- project t = frequency
        [ (1, return $ inject (Construct (c++c) as))
        , (15, do
                mask <- oneHot (length as)
                as'  <- sequence [if hot then mutateTerm a else return a | (a,hot) <- zip as mask]
                return $ inject $ Construct c as'
          )
        ]



----------------------------------------------------------------------------------------------------
-- * Generation of 'DAG's
----------------------------------------------------------------------------------------------------

genLets
    :: (Constructors f, Traversable f)
    => Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> [Name]  -- ^ Variables in scope
    -> Int     -- ^ Number of bindings
    -> Gen (DAG (Binding :+: f))
genLets closed s denv env 0 = genDAG closed s denv env
genLets closed s denv env n = do
    a <- genDAG closed (s `div` 2) denv env
    v <- pickVar 1 4 denv
    b <- genLets closed (s `div` 2) (v:denv) env (n-1)
    return $ Term $ Inl $ DLet v a b

-- | Generate a term with let binders for sharing
genDAG
    :: (Constructors f, Functor f, Traversable f)
    => Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> [Name]  -- ^ Variables in scope
    -> Gen (DAG (Binding :+: f))
genDAG closed 0 denv env = frequency
    [ (freqDVar, fmap (Term . Inl . DVar) $ oneof $ map return denv
      )
    , (1, fmap Term
        $ oneof
        $ map (return . Inr . Inr . fmap (const undefined))
        $ filter (null . toList) constructors
      )
    , (freqVar, do
            v <- pickVar 5 freqFree env
            return $ Term $ Inr $ Inl $ Var v
      )
    ]
  where
    freqDVar = if null denv then 0 else 2
    freqVar  = if closed && null env then 0 else 2
    freqFree = if closed then 0 else 1
genDAG closed s denv env = frequency
    [ (2, do
            c <- oneof $ map (return . Inr . Inr) $ filter (not . null . toList) constructors
            let l = length (toList c)
            fmap Term $ traverse (\_ -> genDAG closed (s `div` l) denv env) c
      )
    , (2, do
            v <- pickVar 1 3 env
            fmap (Term . Inr . Inl . Lam v) $ genDAG closed (s-1) denv (v:env)
      )
    , (2, do
            n <- choose (1,5)
            genLets closed s denv env n
      )
    , (1, genDAG closed 0 denv env)
    ]

-- | Generate a closed term with many 'Let' binders
genClosedDAG :: (Constructors f, Traversable f) => Gen (DAG (Binding :+: f))
genClosedDAG = sized $ \s -> genDAG True (s*20) [] []

-- | Generate a possibly open term with many 'Let' binders
genOpenDAG :: (Constructors f, Traversable f) => Gen (DAG (Binding :+: f))
genOpenDAG = sized $ \s -> genDAG False (s*20) [] []

-- | Like 'genClosedDAG' but with a higher chance of having several let binders at the top
genClosedDAGTop :: (Constructors f, Traversable f) => Gen (DAG (Binding :+: f))
genClosedDAGTop = sized $ \s -> choose (0,15) >>= genLets False (s*20) [] []

-- | Like 'genOpenDAG' but with a higher chance of having several let binders at the top
genOpenDAGTop :: (Constructors f, Traversable f) => Gen (DAG (Binding :+: f))
genOpenDAGTop = sized $ \s -> choose (0,15) >>= genLets False (s*20) [] []

-- | Like 'genOpenDAGTop' but generate also an environment of definitions which the term may use
genDAGEnv :: (Constructors f', Traversable f', Binding :<: f, f ~ (Binding :+: f')) => Gen (Defs f, DAG f)
genDAGEnv = do
    t <- fmap renameUnique genOpenDAGTop  -- TODO Renaming only needed for prop_expose; remove later
    let (ds, Term f) = splitDefs t
    n <- choose (0, length ds)
    let (ds',env) = splitAt n ds
    return (env, addDefs ds' (Term f))

