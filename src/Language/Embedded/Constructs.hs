{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | General syntactic language constructs

module Language.Embedded.Constructs
    ( HasVars (..)
    , Name (..)
    , Construct (..)
    , Binding (..)
    , maxLam
    , lam
    , App (..)
    , Let (..)
    , viewLet
    , Lit (..)
    , Cond (..)
    , Args (..)
    , argsOf
    , argsS
    , Env (..)
    , getEnv
    , lookEnv
    ) where



import Data.Foldable (toList)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Tree

import Data.Comp.Variables

import Data.Syntactic.TypeUniverse
import Data.Syntactic.Functional (Name (..))

import Language.Embedded.Syntax
import Language.Embedded.AG



----------------------------------------------------------------------------------------------------
-- * Syntactic constructs
----------------------------------------------------------------------------------------------------

-- | A generic N-ary construct parameterized on its name
data Construct a = Construct String [a]
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF] [''Construct]

instance ShowF Construct
  where
    showF (Construct c []) = c
    showF (Construct c as) = "(" ++ unwords (c:as) ++ ")"

instance ShowConstr Construct
  where
    showConstr (Construct c _) = c

instance Render  Construct
instance HasVars Construct v

-- | Variables and binders
data Binding a
    = Var Name    -- ^ Variable
    | Lam Name a  -- ^ Lambda binding
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowConstr] [''Binding]

showVar :: Name -> String
showVar v = 'v' : show v

instance ShowF Binding
  where
    showF (Var v)      = showVar v
    showF (Lam v body) = "(\\" ++ showVar v ++ " -> "  ++ body ++ ")"

instance Render Binding
  where
    stringTreeAlg (Var v) = Node (showVar v) []
    stringTreeAlg (Lam v body) = Node ("Lam " ++ showVar v) [body]

instance HasVars Binding Name
  where
    isVar (Var v) = Just v
    isVar _       = Nothing

    bindsVars (Lam v a) = Map.singleton a (Set.singleton v)
    bindsVars _         = Map.empty

-- | Get the highest name bound by the first 'Lam' binders at every path from the root. If the term
-- has /ordered binders/ \[1\], 'maxLam' returns the highest name introduced in the whole term.
--
-- \[1\] Ordered binders means that the names of 'Lam' nodes are decreasing along every path from
-- the root.
maxLam :: (Binding :<: f, Foldable f) => Term f -> Name
maxLam (Term f)
    | Just (Lam n _) <- proj f = n
    | otherwise = maximum $ (0:) $ map maxLam $ toList f

-- | Higher-order interface for typed variable binding
--
-- Assumptions:
--
--   * The body @f@ does not inspect its argument.
--
--   * Applying @f@ to a term with ordered binders results in a term with /ordered binders/ \[1\].
--
-- \[1\] Ordered binders means that the names of 'LamT' nodes are decreasing along every path from
-- the root.
--
-- See \"Using Circular Programs for Higher-Order Syntax\"
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

instance Render  App
instance HasVars App v

-- | Let binding
data Let a = Let a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Let]

instance Render Let
  where
    stringTreeAlg (Let a (Node lam [body]))
        | ("Lam",v) <- splitAt 3 lam = Node ("Let" ++ v) [a,body]
    stringTreeAlg (Let a f) = Node "Let" [a,f]

instance HasVars Let v

-- | Match on a 'Let' constructor
--
-- A result @(v,a,b)@ corresponds to the expression @let v = a in b@
viewLet :: (Binding :<: f, Let :<: f) => Term f -> Maybe (Name, Term f, Term f)
viewLet t = do
    Let a lam <- project t
    Lam v b   <- project lam
    return (v,a,b)

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

instance HasVars (Lit t) v

-- | Conditional
data Cond a = Cond a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Cond]

instance Render  Cond
instance HasVars Cond v



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

