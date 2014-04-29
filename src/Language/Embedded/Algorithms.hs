module Language.Embedded.Algorithms where



import Data.Foldable (Foldable, toList)
import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set

import Language.Embedded.Syntax
import Language.Embedded.Constructs



-- | Get the set of free variables in a term
freeVars :: (Binding :<: f, Functor f, Foldable f) => Term f -> Set Name
freeVars t
    | Just (Var v) <- project t = Set.singleton v
freeVars t
    | Just (Lam v a) <- project t = Set.delete v $ freeVars a
freeVars (Term f) = Foldable.fold $ fmap freeVars f

-- | Get the set of variables used in a term
usedVars :: (Binding :<: f, Functor f, Foldable f) => Term f -> Set Name
usedVars t = Set.fromList [v | Var v <- subterms' t]

-- | Get the set of variables introduced or used in a term
allVars :: (Binding :<: f, Functor f, Foldable f) => Term f -> Set Name
allVars t = Set.fromList [v | v <- map viewBind $ subterms' t]
  where
    viewBind (Var v)   = v
    viewBind (Lam v _) = v

-- | Environment used by 'alphaEq''
type AlphaEnv = [(Name,Name)]

alphaEq' :: (EqF f, Binding :<: f, Functor f, Foldable f) => AlphaEnv -> Term f -> Term f -> Bool
alphaEq' env var1 var2
    | Just (Var v1) <- project var1
    , Just (Var v2) <- project var2
    = case lookup v1 env of
        Nothing  -> v1==v2   -- Free variables
        Just v2' -> v2==v2'
alphaEq' env lam1 lam2
    | Just (Lam v1 body1) <- project lam1
    , Just (Lam v2 body2) <- project lam2
    = alphaEq' ((v1,v2):env) body1 body2
alphaEq' env (Term a) (Term b)
    =  eqF (fmap (const ()) a) (fmap (const ()) b)
    && all (uncurry (alphaEq' env)) (zip (toList a) (toList b))

-- | Alpha-equivalence
alphaEq :: (EqF f, Binding :<: f, Functor f, Foldable f) =>  Term f -> Term f -> Bool
alphaEq = alphaEq' []

-- | Generate an infinite list of fresh names given a list of allocated names
--
-- The argument is assumed to be sorted and not containing an infinite number of adjacent names.
freshVars :: [Name] -> [Name]
freshVars as = go 0 as
  where
    go c [] = [c..]
    go c (v:as)
      | c < v     = c : go (c+1) (v:as)
      | c == v    = go (c+1) as
      | otherwise = go c as

