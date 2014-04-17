{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | General syntactic language constructs

module EDSL.Constructs where



import Data.Foldable (toList)
import Data.Tree

import Data.Syntactic.TypeUniverse
import Data.Syntactic.Constructs (Name (..))

import EDSL.Syntax
import EDSL.AG



----------------------------------------------------------------------------------------------------
-- * Syntactic constructs
----------------------------------------------------------------------------------------------------

-- | A generic N-ary construct parameterized on its name
data Construct a = Construct String [a]
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF] [''Construct]

instance ShowConstr Construct
  where
    showConstr (Construct c _) = c

instance Render Construct

-- | Name binding constructs
data Binding a
    = Var Name    -- ^ Variable
    | Lam Name a  -- ^ Lambda binding
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Binding]

instance Render Binding
  where
    stringTreeAlg (Var v) = Node ('v' : show v) []
    stringTreeAlg (Lam v body) = Node ("Lam v" ++ show v) [body]

-- | The highest name bound by the first binders at every path from the root
--
-- (Assuming that each binder binds a name that is higher than all names bound in its body, 'maxLam'
-- returns the highest name bound in the term.)
maxLam :: (Binding :<: f, Foldable f) => Term f -> Name
maxLam (Term f)
    | Just (Lam n _) <- proj f = n
    | otherwise = maximum $ (0:) $ map maxLam $ toList f

-- | Smart constructor for lambda binding
--
-- See "Using Circular Programs for Higher-Order Syntax"
-- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)
lam :: (Binding :<: f, Foldable f) => (Term f -> Term f) -> Term f
lam f = inject $ Lam n body
  where
    body = f (inject (Var n))
    n    = maxLam body + 1

-- | Application
data App a = App a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''App]

instance Render App

-- | Let binding
data Let a = Let a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Let]

instance Render Let
  where
    stringTreeAlg (Let a (Node lam [body]))
        | ("Lam",v) <- splitAt 3 lam = Node ("Let" ++ v) [a,body]
    stringTreeAlg (Let a f) = Node "Let" [a,f]

instance
    ( Syntactic a
    , Syntactic b
    , PF a ~ PF b
    , Binding :<: PF a
    , Foldable (PF a)
    , Let :<: PF a
    ) =>
      Syntactic (a -> b)
  where
    type PF (a -> b)       = PF a
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = sugar' $ lam (desugar' . f . sugar')
    sugar     = smartSugar (flip Let)
  -- TODO Could also use App

-- | Literal
data Lit t a = Lit (Dynamic t)
  deriving (Functor, Foldable, Traversable)

instance (TypeEq t t, Witness Eq t t) => Eq (Lit t a)
  where
    Lit a == Lit b = a == b

instance Witness Show t t => Show (Lit t a)
  where
    show (Lit a) = show a

instance (TypeEq t t, Witness Eq t t) => EqF (Lit t)
  where
    eqF (Lit a) (Lit b) = a == b

instance Witness Show t t => ShowF (Lit t)
  where
    showF (Lit a) = show a

instance Witness Show t t => ShowConstr (Lit t)
  where
    showConstr (Lit a) = show a

instance Witness Show t t => Render (Lit t)

-- | Conditional
data Cond a = Cond a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Cond]

instance Render Cond



----------------------------------------------------------------------------------------------------
-- * Attribute grammars
----------------------------------------------------------------------------------------------------

-- | Attribute that lists the immediate bound variables in a term
newtype Args = Args {unArgs :: [Name]}

-- | Get the 'Args' attribute of a term
argsOf :: (?below :: a -> q, Args :< q) => a -> [Name]
argsOf = unArgs . below

-- | Synthesize the 'Args' attribute of a term
--
-- The variables of immediate 'Lam' nodes will appear in order. If the root is not a 'Lam' the list
-- will be empty.
argsS :: (Binding :<: f) => Syn f q Args
argsS f
    | Just (Lam v b) <- proj f = Args (v : argsOf b)
    | otherwise = Args []

-- | Attribute representing a variable environment
newtype Env a = Env {unEnv :: [(Name, a)]}

-- | Get the 'Env' attribute
getEnv :: (?above :: q, Env a :< q) => [(Name,a)]
getEnv = unEnv above

-- | Lookup in the 'Env' attribute
lookEnv :: (?above :: i, Env a :< i) => Name -> Maybe a
lookEnv v = lookup v getEnv

