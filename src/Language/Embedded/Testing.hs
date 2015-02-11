{-# LANGUAGE NoMonomorphismRestriction #-}

module Language.Embedded.Testing where




import Control.Applicative
import Control.Monad
import Data.Char (isAlphaNum)
import Data.Foldable (toList)
import Data.List (nub)
import qualified Data.Set as Set
import Data.Traversable (traverse)
import Data.Typeable (Typeable)
import Test.QuickCheck

import Test.Feat
import Test.Feat.Enumerate (pay)

import Data.Comp.Ops

import Language.Embedded hiding (Typeable)
import Language.Embedded.Sharing



----------------------------------------------------------------------------------------------------
-- * Debugging
----------------------------------------------------------------------------------------------------

mkVar       = inject . Var
mkLam v     = inject . Lam v
mkc0        = inject $ Construct "c0" []
mkc1 a      = inject $ Construct "c1" [a]
mkc2 a b    = inject $ Construct "c2" [a,b]
mkc3 a b c  = inject $ Construct "c3" [a,b,c]
mkRef       = inject . Ref
mkDef v a b = inject $ Def v a b

-- | Convert an arbirary term to a term with 'Construct' nodes
--
-- The idea is that showing the resulting term should produce valid Haskell code for the term. The
-- string for each constructor is obtained from 'ShowConstr' and prepended by @"mk"@. The idea is to
-- get a term where each node is a call to a \"smart constructor\", assumed to have a name that
-- starts with @mk@.
--
-- For atoms that are not fully alphanumeric strings, parentheses are put around the constructor.
-- This makes sure that e.g. @`Term` $ `Lam` 2 $ `Term` $ `Var` 2@ gets printed as
-- @(mkLam 2 (mkVar 2))@.
toConstr :: (ShowConstr f, Functor f, Foldable f) => Term f -> Term Construct
toConstr = cata go
  where
    go f = Term $ Construct constr as
      where
        c      = "mk" ++ showConstr f
        as     = toList f
        brack  = not (all isAlphaNum c) && null as
        constr = if brack then "(" ++ c ++ ")" else c



----------------------------------------------------------------------------------------------------
-- * Simple term generation
----------------------------------------------------------------------------------------------------

class Constructors f
  where
    constructors :: [f ()]

instance (Constructors f, Constructors g) => Constructors (f :+: g)
  where
    constructors = map Inl constructors ++ map Inr constructors

constr :: [a] -> Construct a
constr as = Construct ('c' : show (length as)) as

instance Constructors Construct
  where
    constructors = [constr $ replicate c () | c <- [0..3]]

instance Constructors App  where constructors = [App () ()]
instance Constructors Let  where constructors = [Let () ()]
instance Constructors Cond where constructors = [Cond () () ()]

-- | Generate a random term
genTerm :: (Constructors f, Traversable f) => Int -> Gen (Term f)
genTerm 0
    = fmap Term
    $ oneof
    $ map (return . fmap (const undefined))
    $ filter (null . toList) constructors
genTerm s = frequency
    [ (10, do
            c <- oneof $ map return $ filter (not . null . toList) constructors
            let l = length (toList c)
            fmap Term $ traverse (\_ -> genTerm (s `div` l)) c
      )
    , (1, genTerm 0)
    ]

-- | \"Simple term\"
newtype STerm = STerm { unSTerm :: Term Construct }
  deriving (Eq, Ord, Typeable)

instance Show STerm where show = show . toConstr . unSTerm

instance Arbitrary STerm
  where
    arbitrary = sized (fmap STerm . genTerm)

    shrink (STerm (Term (Construct c as))) = map STerm as ++
        map (STerm . Term . constr . map unSTerm) (shrink $ map STerm as)



----------------------------------------------------------------------------------------------------
-- * Generation of untyped lambda terms
----------------------------------------------------------------------------------------------------

instance Arbitrary Name
  where
--     arbitrary = fmap (\(Positive v) -> Name v) arbitrary
    arbitrary = fmap Name $ choose (0,5)

-- | Generate a bound (probability b/(b+f)) or free (probability f/(b+f)) variable
pickVar :: Arbitrary name => Int -> Int -> [name] -> Gen name
pickVar _ 0 [] = error "pickVar: no variables in scope"
pickVar _ _ [] = arbitrary
pickVar b f env = frequency
    [ (b, oneof $ map return env)
    , (f, arbitrary)
    ]

genBind
    :: (Constructors f, Traversable f)
    => Bool    -- ^ Only closed terms?
    -> Int     -- ^ Size
    -> [Name]  -- ^ Variables in scope
    -> Gen (Term (Binding :+: f))
genBind closed 0 env = frequency
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
genBind closed s env = frequency
    [ (6, do
            c <- oneof $ map (return . Inr) $ filter (not . null . toList) constructors
            let l = length (toList c)
            fmap Term $ traverse (\_ -> genBind closed (s `div` l) env) c
      )
    , (6, do
            v <- pickVar 1 3 env
            fmap (Term . Inl . Lam v) $ genBind closed (s-1) (v:env)
      )
    , (1, genBind closed 0 env)
    ]

-- | Closed lambda term
newtype Closed = Closed { unClosed :: Term (Binding :+: Construct) }
  deriving (Eq, Ord, Typeable)

instance Show Closed where show = show . toConstr . unClosed

instance Arbitrary Closed
  where
    arbitrary = sized $ \s -> fmap Closed $ genBind True (20*s) []

    shrink (Closed (Term f)) = case f of
        Inl (Var v)      -> [Closed $ Term $ Inr $ constr []]
        Inl (Lam v body) ->
            body' ++ map (Closed . Term . Inl . Lam v . unClosed) (shrink (Closed body))
          where
            body' = if v `Set.member` freeVars body then [] else [Closed body]
        Inr (Construct c as) -> map Closed as ++
            map (Closed . Term . Inr . constr . map unClosed) (shrink $ map Closed as)

-- | Possibly open lambda term
newtype Open = Open { unOpen :: Term (Binding :+: Construct) }
  deriving (Eq, Ord, Typeable)

instance Show Open where show = show . toConstr . unOpen

instance Arbitrary Open
  where
    arbitrary = sized $ \s -> fmap Open $ genBind False (20*s) []

    shrink (Open (Term f)) = case f of
        Inl (Var v)   -> [Open $ Term $ Inr $ constr []]
        Inl (Lam v a) -> Open a : map (Open . Term . Inl . Lam v . unOpen) (shrink (Open a))
        Inr (Construct c as) -> map Open as ++
            map (Open . Term . Inr . constr . map unOpen) (shrink $ map Open as)

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

-- | Mutates a term to get another one that is guaranteed not to be alpha-equivalent
mutateTerm :: Term (Binding :+: Construct) -> Gen (Term (Binding :+: Construct))
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

instance Arbitrary RName
  where
    arbitrary = fmap (\(Positive v) -> RName v) arbitrary

genDefs
    :: (Constructors f, Traversable f)
    => Bool     -- ^ Only closed terms?
    -> Int      -- ^ Size
    -> [RName]  -- ^ Variables in scope
    -> [Name]   -- ^ Variables in scope
    -> Int      -- ^ Number of bindings
    -> Gen (DAG (Binding :+: f))
genDefs closed s denv env 0 = genDAG closed s denv env
genDefs closed s denv env n = do
    a <- genDAG closed (s `div` 2) denv env
    v <- pickVar 1 4 denv
    b <- genDefs closed (s `div` 2) (v:denv) env (n-1)
    return $ Term $ Inl $ Def v a b

-- | Generate a 'DAG'
genDAG
    :: (Constructors f, Functor f, Traversable f)
    => Bool     -- ^ Only closed terms?
    -> Int      -- ^ Size
    -> [RName]  -- ^ Variables in scope
    -> [Name]   -- ^ Variables in scope
    -> Gen (DAG (Binding :+: f))
genDAG closed 0 denv env = frequency
    [ (freqRef, fmap (Term . Inl . Ref) $ oneof $ map return denv
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
    freqRef  = if null denv then 0 else 2
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
            genDefs closed s denv env n
      )
    , (1, genDAG closed 0 denv env)
    ]

-- | Closed 'DAG' with lots of sharing
newtype ClosedDAG = ClosedDAG { unClosedDAG :: DAG (Binding :+: Construct) }
  deriving (Eq, Ord, Typeable)

instance Show ClosedDAG where show = show . toConstr . unClosedDAG

instance Arbitrary ClosedDAG
  where
    arbitrary = sized $ \s -> fmap ClosedDAG $ genDAG True (s*20) [] []

    shrink (ClosedDAG t)
        | Just (Ref v) <- project t = [ClosedDAG $ inject $ constr []]
        | Just (Var v) <- project t = [ClosedDAG $ inject $ constr []]

        | Just (Def v a b) <- project t
        , let b' = if v `Set.member` freeRefs b then [] else [b]
        = map ClosedDAG
            $  b'
            ++ [a]
            ++ [ inject $ Def v a' b'
                  | (ClosedDAG a', ClosedDAG b') <- shrink (ClosedDAG a, ClosedDAG b)
               ]

        | Just (Lam v body) <- project t
        , let body' = if v `Set.member` freeVars body then [] else [ClosedDAG body]
        = body' ++ map (ClosedDAG . inject . Lam v . unClosedDAG) (shrink (ClosedDAG body))

        | Just (Construct c as) <- project t
        = map ClosedDAG as
          ++ map (ClosedDAG . inject . constr . map unClosedDAG) (shrink $ map ClosedDAG as)

-- | Possibly open 'DAG' with lots of sharing
newtype OpenDAG = OpenDAG { unOpenDAG :: DAG (Binding :+: Construct) }
  deriving (Eq, Ord, Typeable)

instance Show OpenDAG where show = show . toConstr . unOpenDAG

instance Arbitrary OpenDAG
  where
    arbitrary = sized $ \s -> fmap OpenDAG $ genDAG False (s*20) [] []

    shrink (OpenDAG t)
        | Just (Ref v) <- project t = [OpenDAG $ inject $ constr []]
        | Just (Var v) <- project t = [OpenDAG $ inject $ constr []]

        | Just (Def v a b) <- project t
        , let b' = if v `Set.member` freeRefs b then [] else [b]
        = map OpenDAG
            $  b'
            ++ [a]
            ++ [inject $ Def v a' b' | (OpenDAG a', OpenDAG b') <- shrink (OpenDAG a, OpenDAG b)]

        | Just (Lam v a) <- project t
        = OpenDAG a : map (OpenDAG . inject . Lam v . unOpenDAG) (shrink (OpenDAG a))

        | Just (Construct c as) <- project t
        = map OpenDAG as
          ++ map (OpenDAG . inject . constr . map unOpenDAG) (shrink $ map OpenDAG as)

-- | Closed 'DAG' with high chance of having several 'Def' binders at the top
newtype ClosedDAGTop = ClosedDAGTop { unClosedDAGTop :: DAG (Binding :+: Construct) }
  deriving (Eq, Ord, Typeable)

instance Show ClosedDAGTop where show = show . toConstr . unClosedDAGTop

instance Arbitrary ClosedDAGTop
  where
    arbitrary = sized $ \s -> choose (0,15) >>= fmap ClosedDAGTop . genDefs True (s*20) [] []
    shrink    = map (ClosedDAGTop . unClosedDAG) . shrink . ClosedDAG . unClosedDAGTop

-- | Possibly open 'DAG' with high chance of having several 'Def' binders at the top
newtype OpenDAGTop = OpenDAGTop { unOpenDAGTop :: DAG (Binding :+: Construct) }
  deriving (Eq, Ord, Typeable)

instance Show OpenDAGTop where show = show . toConstr . unOpenDAGTop

instance Arbitrary OpenDAGTop
  where
    arbitrary = sized $ \s -> choose (0,15) >>= fmap OpenDAGTop . genDefs False (s*20) [] []
    shrink    = map (OpenDAGTop . unOpenDAG) . shrink . OpenDAG . unOpenDAGTop

-- | A 'DAG' paired with an environment of definitions that are possibly used in the term
--
-- If @d = `DAGEnv` env t@, then @`addDefs` env t@ is a 'DAG' with the same properties as
-- 'OpenDAGTop'.
data DAGEnv = DAGEnv (Defs (Binding :+: Construct)) (DAG (Binding :+: Construct))
  deriving (Eq, Ord, Typeable)

instance Show DAGEnv
  where
    show (DAGEnv env t) = unlines
        [ "--------------------"
        , "env = " ++ show [(v, toConstr a) | (v,a) <- env]
        , "--"
        , "dag = " ++ show (toConstr t)
        , "--------------------"
        ]

-- | Generate a 'Defs' list
--
-- Earlier definitions may depend on later ones. The variables in the list are all distinct.
genEnv :: forall f
    .  (Constructors f, Traversable f)
    => Int -> Gen (Defs (Binding :+: f))
genEnv s = do
    n  <- choose (0,5)
    vs <- fmap nub $ replicateM n $ fmap (\(Positive a) -> a) arbitrary
    go vs []
  where
    go :: [RName] -> Defs (Binding :+: f) -> Gen (Defs (Binding :+: f))
    go []     env = return env
    go (v:vs) env = do
        a <- genDAG False (s `div` 4) ns []
        go vs ((v,a) : env)
      where
        ns = map fst env

instance Arbitrary DAGEnv
  where
    arbitrary = sized $ \s -> do
        env <- genEnv s
        t   <- genDAG False s (map fst env) []
        return $ DAGEnv env t

    shrink (DAGEnv env t)
        =  [ DAGEnv env t' | OpenDAG t' <- shrink $ OpenDAG t ]
        ++ [ DAGEnv (reverse env') t | env' <- go (reverse env) ]
      where
        go [] = []
        go ((v,a):env)
            =  dropBinding
            ++ [ (v,a'):env | OpenDAG a' <- shrink $ OpenDAG a ]
            ++ [ (v,a):env' | env' <- go env ]
          where
            dropBinding = if v `Set.member` freeRefs (addDefs (reverse env) t) then [] else [env]



----------------------------------------------------------------------------------------------------
-- * Enumeration using Feat
----------------------------------------------------------------------------------------------------

-- | Increase the cost of an enumeration by @n@
pays :: Int -> Enumerate a -> Enumerate a
pays n e = iterate pay e !! n

-- | Enumeration space for numbers
spaceNum :: Num a => Enumerate a
spaceNum = consts
    [ pure 0
    , (+1) <$> spaceNum
    ]

instance Enumerable Name  where enumerate = spaceNum
instance Enumerable RName where enumerate = spaceNum

spaceOpen :: Enumerate (Term (Binding :+: Construct))
spaceOpen = consts
    [ mkVar <$> enumerate
    , pays 3 $ mkLam <$> enumerate <*> spaceOpen
    , pays 3 $ pure mkc0
    , pays 3 $ mkc1 <$> spaceOpen
    , pays 3 $ mkc2 <$> spaceOpen <*> spaceOpen
    ]

-- | Enumeration space for 'DAG's
spaceDAG :: Enumerate (DAG (Binding :+: Construct))
spaceDAG = consts
    [ mkRef <$> enumerate
    , pays 3 $ mkDef <$> enumerate <*> spaceDAG <*> spaceDAG
    , mkVar <$> enumerate
    , pays 3 $ mkLam <$> enumerate <*> spaceDAG
    , pays 3 $ pure mkc0
    , pays 3 $ mkc1 <$> spaceDAG
    , pays 3 $ mkc2 <$> spaceDAG <*> spaceDAG
    ]

-- | Enumeration space for a list of 'DAG's
spaceDAGs :: Enumerate [DAG (Binding :+: Construct)]
spaceDAGs = consts
    [ pure []
    , pays 3 $ (:) <$> spaceDAG <*> spaceDAGs
    ]

instance Enumerable Open    where enumerate = fmap Open spaceOpen
instance Enumerable OpenDAG where enumerate = fmap OpenDAG spaceDAG
instance Enumerable DAGEnv  where enumerate = liftA2 DAGEnv (fmap (zip [0..]) spaceDAGs) spaceDAG

-- | Uniform QuickCheck generator for 'DAGEnv'
genDAGEnv :: Gen DAGEnv
genDAGEnv = sized (uniform . (`div` 4))

-- | A less verbose variant of 'featCheck', that crashes when it encounters an error
featChecker :: (Enumerable a, Show a)
    => Int     -- ^ Size bound
    -> String  -- ^ Name of property
    -> (a -> Bool)
    -> IO ()
featChecker s propName prop = ioFeat' (take s values) report
  where
    -- A less verbose version of 'ioFeat'
    ioFeat' vs f = go vs 0 0
      where
        go ((c,xs):xss) s tot = mapM f xs >> go xss (s+1) (tot + c)
        go []           s tot = putStrLn $ propName ++ ": OK (tested " ++ show tot ++ " values)"

    report a
        | prop a    = return ()
        | otherwise = error $ unlines
            [ ""
            , propName ++ ": FAILED"
            , show a
            ]

