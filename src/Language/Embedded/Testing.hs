module Language.Embedded.Testing where



import Control.Monad
import Data.Foldable (toList)
import Data.Traversable (traverse)
import Test.QuickCheck

import Data.Comp.Ops

import Language.Embedded
import Language.Embedded.Sharing



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

type TestSig = Binding :+: Construct

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

genLets
    :: (Constructors f, Traversable f)
    => Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> Int     -- ^ Number of bindings
    -> Gen (Term (Binding :+: Let :+: f))
genLets closed s env 0 = genDAG closed s env
genLets closed s env n = do
    a <- genDAG closed (s `div` 2) env
    v <- pickVar 1 4 env
    b <- genLets closed (s `div` 2) (v:env) (n-1)
    return $ Term $ Inr $ Inl $ Let a $ Term $ Inl $ Lam v b

-- | Generate a term with let binders for sharing
genDAG
    :: (Constructors f, Functor f, Traversable f)
    => Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> Gen (Term (Binding :+: Let :+: f))
genDAG closed 0 env = frequency
    [ (1, fmap Term
        $ oneof
        $ map (return . Inr . Inr . fmap (const undefined))
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
genDAG closed s env = frequency
    [ (2, do
            c <- oneof $ map (return . Inr . Inr) $ filter (not . null . toList) constructors
            let l = length (toList c)
            fmap Term $ traverse (\_ -> genDAG closed (s `div` l) env) c
      )
    , (2, do
            v <- pickVar 1 3 env
            fmap (Term . Inl . Lam v) $ genDAG closed (s-1) (v:env)
      )
    , (2, do
            n <- choose (1,5)
            genLets closed s env n
      )
    , (1, genDAG closed 0 env)
    ]

-- | Generate a closed term with many 'Let' binders
genClosedDAG :: (Constructors f, Traversable f) => Gen (Term (Binding :+: Let :+: f))
genClosedDAG = sized $ \s -> genDAG True (s*20) []

-- | Generate a possibly open term with many 'Let' binders
genOpenDAG :: (Constructors f, Traversable f) => Gen (Term (Binding :+: Let :+: f))
genOpenDAG = sized $ \s -> genDAG False (s*20) []

-- | Like 'genClosedDAG' but with a higher chance of having several let binders at the top
genClosedDAGTop :: (Constructors f, Traversable f) => Gen (Term (Binding :+: Let :+: f))
genClosedDAGTop = sized $ \s -> choose (0,15) >>= genLets False (s*20) []

-- | Like 'genOpenDAG' but with a higher chance of having several let binders at the top
genOpenDAGTop :: (Constructors f, Traversable f) => Gen (Term (Binding :+: Let :+: f))
genOpenDAGTop = sized $ \s -> choose (0,15) >>= genLets False (s*20) []

-- | Like 'genOpenDAGTop' but generate also an environment of definitions which the term may use
genDAGEnv :: (Constructors f', Traversable f', Binding :<: f, Let :<: f, f ~ (Binding :+: Let :+: f')) => Gen (Defs f, Term f)
genDAGEnv = do
    t <- fmap renameUnique genOpenDAGTop  -- TODO Renaming only needed for prop_expose; remove later
    let (ds, Term f) = splitDefs t
    n <- choose (0, length ds)
    let (ds',env) = splitAt n ds
    return (env, addDefs ds' (Term f))

