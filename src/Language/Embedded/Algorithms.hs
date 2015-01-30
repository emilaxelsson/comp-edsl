module Language.Embedded.Algorithms where



import Control.Monad.State
import Data.Foldable (Foldable, toList)
import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse)

import Language.Embedded.Syntax
import Language.Embedded.Constructs
import Language.Embedded.Environment



-- | Get the set of free variables in a term
freeVars :: (Binding :<<: f, Functor f, Foldable f) => Term f -> Set Name
freeVars t
    | Just (Var v) <- prjTerm t = Set.singleton v
freeVars t
    | Just (Lam v a) <- prjTerm t = Set.delete v $ freeVars a
freeVars (Term f) = Foldable.fold $ fmap freeVars f

-- | Get the set of variables used in a term
usedVars :: (Binding :<<: f, Functor f, Foldable f) => Term f -> Set Name
usedVars t = Set.fromList [v | Just (Var v) <- map prjTerm $ subterms t]

-- | Get the set of variables introduced or used in a term
allVars :: (Binding :<<: f, Functor f, Foldable f) => Term f -> Set Name
allVars t = Set.fromList [v | Just v <- map (fmap viewBind . prjTerm) $ subterms t]
  where
    viewBind (Var v)   = v
    viewBind (Lam v _) = v

-- | Check if two constructors are equal
constrEq :: (EqF f, Functor f) => f a -> f a -> Bool
constrEq a b = eqF (fmap (const ()) a) (fmap (const ()) b)

-- | Environment used by 'alphaEq''
type AlphaEnv = [(Name,Name)]

alphaEq' :: (EqF f, Binding :<<: f, Functor f, Foldable f) => AlphaEnv -> Term f -> Term f -> Bool
alphaEq' env var1 var2
    | Just (Var v1) <- prjTerm var1
    , Just (Var v2) <- prjTerm var2
    = case (lookup v1 env, lookup v2 env') of
        (Nothing, Nothing)   -> v1==v2  -- Free variables
        (Just v2', Just v1') -> v1==v1' && v2==v2'
        _                    -> False
  where
    env' = [(v2,v1) | (v1,v2) <- env]
alphaEq' env lam1 lam2
    | Just (Lam v1 body1) <- prjTerm lam1
    , Just (Lam v2 body2) <- prjTerm lam2
    = alphaEq' ((v1,v2):env) body1 body2
alphaEq' env (Term a) (Term b)
    =  constrEq a b
    && all (uncurry (alphaEq' env)) (zip (toList a) (toList b))

-- | Alpha-equivalence
alphaEq :: (EqF f, Binding :<<: f, Functor f, Foldable f) => Term f -> Term f -> Bool
alphaEq = alphaEq' []

-- | Generate an infinite list of fresh names given a list of allocated names
--
-- The argument is assumed to be sorted and not contain an infinite number of adjacent names.
freshVars :: [Name] -> [Name]
freshVars as = go 0 as
  where
    go c [] = [c..]
    go c (v:as)
      | c < v     = c : go (c+1) (v:as)
      | c == v    = go (c+1) as
      | otherwise = go c as

freshVar :: MonadState [Name] m => m Name
freshVar = do
    v:vs <- get
    put vs
    return v

-- | Rename the bound variables in a term
--
-- The free variables are left untouched. The bound variables are given unique names using as small
-- names as possible. The first argument is a list of reserved names. Reserved names and names of
-- free variables are not used when renaming bound variables.
renameUnique' :: (Binding :<<: f, Traversable f) => [Name] -> Term f -> Term f
renameUnique' vs t = flip evalState fs $ go emptyEnv t
  where
    fs = freshVars $ Set.toAscList (freeVars t `Set.union` Set.fromList vs)
    go env t@(Term f)
        | Just (Var v, back) <- prjInj f
        = case lookEnv v env of
            Just v' -> return $ Term $ back $ Var v'
            _ -> return t
        | Just (Lam v a, back) <- prjInj f
        = do
            v' <- freshVar
            a' <- go ((v,v') |> env) a
            return $ Term $ back $ Lam v' a'
    go env (Term f) = fmap Term $ traverse (go env) f

-- | Rename the bound variables in a term
--
-- The free variables are left untouched. The bound variables are given unique names using as small
-- names as possible. Names of free variables are not used when renaming bound variables.
renameUnique :: (Binding :<<: f, Traversable f) => Term f -> Term f
renameUnique = renameUnique' []

-- | Capture-avoiding parallel substitution
--
-- If the list contains multiple mappings for the same variable, the first one has precedence. Bound
-- variables may get renamed, even when there is no risk for capturing.
parSubst :: (Binding :<<: f, Traversable f)
    => Env (Term f)  -- ^ Substitution
    -> Term f
    -> Term f
parSubst s = transform sub . renameUnique' fvs
  where
    fvs = concatMap (Set.toList . freeVars . snd) $ toListEnv s
    sub t
      | Just (Var v') <- prjTerm t
      , Just new      <- lookEnv v' s
      = new
    sub t = t

-- | Capture-avoiding substitution
--
-- Bound variables may get renamed, even when there is no risk for capturing.
subst :: (Binding :<<: f, Traversable f)
    => Name    -- ^ Variable to replace
    -> Term f  -- ^ Term to substitute for the variable
    -> Term f  -- ^ Term to substitute in
    -> Term f
subst v new = parSubst $ singleEnv v new

-- | Pattern matching with alpha equivalence
--
-- Free variables are treated as meta variables in the pattern. Each occurrence of a meta variable
-- results in a mapping in the result list, and there is no check that the occurrences of a given
-- variable are equal.
--
-- If there are no free variables, 'match' corresponds to 'alphaEq'.
match :: (Binding :<<: f, EqF f, Functor f, Foldable f)
    => Term f  -- ^ Pattern
    -> Term f  -- ^ Term
    -> Maybe [(Name, Term f)]
match = go emptyEnv
  where
    go env p t
      | Just (Var v) <- prjTerm p
      , Just (Var w) <- prjTerm t
      , Just v'      <- lookEnv v env
      , w == v'
      = Just []
    go env p t
      | Just (Var v) <- prjTerm p
      , Nothing      <- lookEnv v env
      = Just [(v,t)]
    go env p t
      | Just (Lam v p') <- prjTerm p
      , Just (Lam w t') <- prjTerm t
      = go ((v,w) |> env) p' t'
    go env (Term pf) (Term tf)
      | constrEq pf tf
      = fmap concat $ sequence [go env p t | (p,t) <- toList pf `zip` toList tf]
    go _ _ _ = Nothing

