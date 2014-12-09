-- | Utilities for working with abstract syntax trees with sharing
--
-- The type 'DAG' represents ASTs with sharing. It is essentially a normal term with let
-- binders; however, instead of 'Let', this module uses a functor transformer 'Where' that allows
-- attaching a number of local definitions to each node in an AST.
--
-- The functions 'dagToTerm' and 'termToDAG' go back and forth between terms with 'Where' and 'Let'
-- for local binders.
--
-- It is often desired to ignore the sharing structure when transforming 'DAG's. The sharing
-- structure is then only there to give a compact representation, and should not affect the
-- semantics of the term. Such transformations can be written using 'expose', which looks through
-- the sharing structure and exposes the top-most constructor for pattern matching.

module Language.Embedded.Sharing where



import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Comp.Variables

import Language.Embedded



getAnn :: (f :&: a) b -> a
getAnn (f :&: a) = a

dropAnn :: (f :&: a) b -> f b
dropAnn (f :&: a) = f

instance HasVars f v => HasVars (f :&: a) v
  where
    isVar     = isVar . dropAnn
    bindsVars = bindsVars . dropAnn

-- | Fold a term by treating sharing transparently. The semantics is as if all sharing is inlined,
-- but the implementation avoids duplication.
--
-- It may not be a good idea to use 'foldWithLet' to transform terms, since the substitution of
-- shared terms does not deal with capturing (only a problem when there are other binders than `Let`
-- in the term). E.g. @`foldWithLet` `Term`@ will inline all shared terms, but will generally not
-- preserve the semantics.
foldWithLet :: (Binding :<<: f, Let :<<: f, Functor f) => (f a -> a) -> Term f -> a
foldWithLet alg = go []
  where
    go env t
      | Just (Var v) <- prjTerm t
      , Just a       <- lookup v env
      = a
    go env t@(Term f)
      | Just (Lam v a) <- prjTerm t
      = alg $ flip fmap f $ \_ -> go (filter ((v/=) . fst) env) a
    go env t
      | Just (v,a,b) <- viewLet t
      = go ((v, go env a) : env) b
    go env (Term f) = alg $ fmap (go env) f

-- | Replacement for a variable. 'Alias' gives a different name for the variable. 'Unfold' gives a
-- definition for the variable.
data VarReplace f
    = Alias Name
    | Unfold (Term f)
  deriving (Eq, Ord, Show)
  -- Note: It may seem easier to use 'Unfold' to cover both cases (aliasing would be the same as
  -- unfolding to a different name), but that has the disadvantage that one must be able to
  -- construct variables, so functions will need a 'Binding :<:' constraint rather than just
  -- 'Binding :<<:'.

-- | Variables in scope. Let-bound variables map to their unfolding, while other variables map to
-- a new name. Earlier definitions may depend on later ones, and earlier definitions shadow later
-- ones.
type Scope f = [(Name, VarReplace f)]

-- | Return an unused name given a list of used names
unusedName :: [Name] -> Name
unusedName [] = 0
unusedName ns = maximum ns + 1

inlineAllHelp :: (Binding :<<: f, Let :<<: f, Traversable f) => Scope f -> Term f -> Term f
inlineAllHelp scope t@(Term f)
    | Just (Var v, back) <- prjInj f
    , Just rep           <- lookup v scope
    = case rep of
        Unfold a -> a
        Alias v' -> Term $ back $ Var v'
inlineAllHelp scope t@(Term f)
    | Just (Lam v a, back) <- prjInj f
    , let v''    = unusedName [v' | (_,Alias v') <- scope]
    , let scope' = (v, Alias v'') : scope
    = Term $ back $ Lam v'' $ inlineAllHelp scope' a
inlineAllHelp scope t
    | Just (v,a,b) <- viewLet t
    = inlineAllHelp ((v, Unfold (inlineAllHelp scope a)) : scope) b
inlineAllHelp env (Term f) = Term $ fmap (inlineAllHelp env) f

-- TODO Can there be alias chains? If so, the first case needs to chase until it finds an alias to
--      itself.
--
--      Also, since only the last name in a chain is going to be used, the search for unused names
--      could be improved a bit.
--
--      Should one also consider variables that are not aliased (variables that appear in unfoldings
--      when looking for unused names?

-- | A sequence of local definitions. Earlier definitions may depend on later ones, and earlier
-- definitions shadow later ones.
type Defs f = [(Name, Term f)]

inlineAllEnvHelp :: (Binding :<<: f, Let :<<: f, Traversable f) =>
    Scope f -> Defs f -> Term f -> Term f
inlineAllEnvHelp scope defs = go scope (reverse defs)
  where
    go scope []           = inlineAllHelp scope
    go scope ((v,s):defs) = go ((v, Unfold (inlineAllHelp scope s)) : scope) defs
  -- This function should be equivalent to `inlineAllHelp scope $ addDefs defs t`, but that would
  -- require a different type. Note the similarity between the last case of `go` and the case for
  -- `Let` in `inlineAllHelp`.


-- | Inline all let bindings in a given environment
--
-- Uses the "rapier" method described in "Secrets of the Glasgow Haskell Compiler inliner" (Peyton
-- Jones and Marlow, JFP 2006) to rename variables where there's risk of capturing.
inlineAllEnv :: (Binding :<<: f, Let :<<: f, Traversable f) => Defs f -> Term f -> Term f
inlineAllEnv env t = inlineAllEnvHelp init env t
  where
    free = foldl (\vs (v,s) -> Set.delete v vs `Set.union` freeVars s) (freeVars t) env
      -- `free` should be equivalent to `freeVars $ addDefs env t`, but that would require a
      -- different type
    init  = case Set.toList free of
      [] -> []
      vs -> let v = maximum vs in [(v, Alias v)]
        -- Insert the highest free variable in the initial environment to make sure that fresh names
        -- are not already used as free variables

-- | Inline all let bindings
--
-- Uses the "rapier" method described in "Secrets of the Glasgow Haskell Compiler inliner" (Peyton
-- Jones and Marlow, JFP 2006) to rename variables where there's risk of capturing.
inlineAll :: (Binding :<<: f, Let :<<: f, Traversable f) => Term f -> Term f
inlineAll = inlineAllEnv []

-- | Add a number of local binders to a term. Existing binders shadow and may depend on the new
-- ones. This function is the left inverse of 'splitDefs'.
addDefs :: (Binding :<: f, Let :<: f, Functor f) => Defs f -> Term f -> Term f
addDefs []         t = t
addDefs ((v,a):ds) t = addDefs ds $ inject $ Let a $ inject $ Lam v t

-- | TODO Remove
addDefs2 :: (Binding :<: f, Let :<: f, Functor f, f' ~ (f :&: a)) => a -> Defs f' -> Term f' -> Term f'
addDefs2 ann []         t = t
addDefs2 ann ((v,a):ds) t = addDefs2 ann ds $ Term $ (:&: ann) $ inj $ Let a $ Term $ (:&: ann) $ inj $ Lam v t

-- | Gather all let bindings at the root of a term. The result is the the local definitions and the
-- first non-let node. 'addDefs' is the left inverse of this function.
splitDefs :: (Binding :<<: f, Let :<<: f, Functor f) => Term f -> (Defs f, Term f)
splitDefs = go []
  where
    go ds t
        | Just (v,a,b) <- viewLet t = go ((v,a):ds) b
        | otherwise                 = (ds,t)

-- | Expose the top-most constructor in a 'DAG' given an environment of definitions in scope.
-- It works roughly as follows:
--
-- * If the top-most node is a variable that has a definition in scope (either in the environment or
--   in the local 'Defs' attached to the node), this definition is returned and 'expose'd.
--
-- * Otherwise, the local definitions of the node are distributed down to the children, which
--   ensures that the (call-by-name) semantics of the 'DAG' is not affected.
--
-- This function assumes that variables and binders are exactly those recognized by the methods of
-- the 'HasVars' class, except for 'Where' which also binds variables.
expose :: (HasVars f Name, Binding :<<: f, Binding :<: f, Let :<<: f, Let :<: f, Traversable f) => Defs f -> Term f -> f (Term f)
expose env t
    | Just v  <- isVar f
    , let ds'  = dropWhile ((v /=) . fst) ds  -- Strip irrelevant bindings from `ds`
    , Just t  <- lookup v (ds' ++ env)        -- `ds` shadows `env`
    , let ds'' = drop 1 ds'                   -- The part of `ds` that `t` may depend on
    = expose env $ addDefs ds'' t
        -- TODO This is a bit inefficient because `expose` will immediately apply `splitDefs`

    | otherwise = fmap pushDefs $ getBoundVars f
  where
    (ds, Term f)    = splitDefs t
    pushDefs (vs,a) = addDefs (filter (\(v,d) -> not $ Set.member v vs) ds) a
                                 -- Remove locally bound variables from the definitions

-- | TODO Remove
expose2 :: (HasVars f Name, Binding :<: f, Binding :<<: f, Let :<: f, Let :<<: f, Traversable f, f' ~ (f :&: a)) => a -> Defs f' -> Term f' -> f' (Term f')
expose2 ann env t
    | Just v  <- isVar f
    , let ds'  = dropWhile ((v /=) . fst) ds  -- Strip irrelevant bindings from `ds`
    , Just t  <- lookup v (ds' ++ env)        -- `ds` shadows `env`
    , let ds'' = drop 1 ds'                   -- The part of `ds` that `t` may depend on
    = expose2 ann env $ addDefs2 ann ds'' t
        -- TODO This is a bit inefficient because `expose` will immediately apply `splitDefs`

    | otherwise = fmap pushDefs $ getBoundVars f
  where
    (ds, Term f)    = splitDefs t
    pushDefs (vs,a) = addDefs2 ann (filter (\(v,d) -> not $ Set.member v vs) ds) a
                                 -- Remove locally bound variables from the definitions

-- | Use a 'DAG' transformer to transform a 'Defs' list
transDefs
    :: (Defs g -> Term f -> Term g)
    -> (Defs g -> Defs f -> Defs g)
transDefs trans env ds = foldr (\(v,a) e -> (v, trans e a) : e) env ds
  -- Important to fold from the right, since earlier definitions may depend on later ones

