module Language.Embedded.Algorithms where



import Data.Foldable (Foldable, toList)

import Data.Syntactic.Functional (Name (..))

import Language.Embedded.Syntax
import Language.Embedded.Constructs



----------------------------------------------------------------------------------------------------
-- * Alpha-equivalence
----------------------------------------------------------------------------------------------------

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

