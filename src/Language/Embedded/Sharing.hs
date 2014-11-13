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



import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Comp.Number

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
foldWithLet :: (Binding :<: f, Let :<: f, Functor f) => (f a -> a) -> Term f -> a
foldWithLet alg = go []
  where
    go env t
      | Just (Var v) <- project t
      , Just a       <- lookup v env
      = a
    go env t
      | Just (Lam v a) <- project t
      = alg $ inj $ Lam v $ go (filter ((v/=) . fst) env) a
    go env t
      | Just (v,a,b) <- viewLet t
      = go ((v, go env a) : env) b
    go env (Term f) = alg $ fmap (go env) f

-- | Inline all 'Let' bindings. Existing variables may get renamed, even when there is no risk of
-- capturing.
inlineLet :: (Binding :<: f, Let :<: f, Traversable f) => Term f -> Term f
inlineLet = foldWithLet Term . renameUnique
  -- Renaming to avoid capturing

-- | A sequence of local definitions. Earlier definitions may depend on later ones, and earlier
-- definitions shadow later ones.
type Defs f = [(Name, Term f)]

-- | Add a number of local binders to a term. Existing binders shadow and may depend on the new
-- ones. This function is the left inverse of 'splitDefs'.
addDefs :: (Binding :<: f, Let :<: f, Functor f) => Defs f -> Term f -> Term f
addDefs []         t = t
addDefs ((v,a):ds) t = addDefs ds $ inject $ Let a $ inject $ Lam v t

-- | Gather all let bindings at the root of a term. The result is the the local definitions and the
-- first non-let node. 'addDefs' is the left inverse of this function.
splitDefs :: (Binding :<: f, Let :<: f, Functor f) => Term f -> (Defs f, Term f)
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
expose :: (HasVars f Name, Binding :<: f, Let :<: f, Traversable f) => Defs f -> Term f -> f (Term f)
expose env t
    | Just v  <- isVar f
    , let ds'  = dropWhile ((v /=) . fst) ds  -- Strip irrelevant bindings from `ds`
    , Just t  <- lookup v (ds' ++ env)        -- `ds` shadows `env`
    , let ds'' = drop 1 ds'                   -- The part of `ds` that `t` may depend on
    = expose env $ addDefs ds'' t
        -- TODO This is a bit inefficient because `expose` will immediately apply `splitDefs`

    | otherwise = fmap pushDefs fn
  where
    (ds, Term f) = splitDefs t
    fn           = number f
    pushDefs a   = addDefs (filter (not . boundIn (bindsVars fn) a . fst) ds) $ unNumbered a

-- | @`boundIn bs a v`@ checks if variable @v@ is bound in sub-term @a@ of a constructor for which
-- 'bindsVars' returns @bs@.
boundIn :: Ord a => Map a (Set Name) -> a -> Name -> Bool
boundIn bs a v = maybe False (\vs -> Set.member v vs) $ Map.lookup a bs

-- | Use a 'DAG' transformer to transform a 'Defs' list
transDefs
    :: (Defs g -> Term f -> Term g)
    -> (Defs g -> Defs f -> Defs g)
transDefs trans env ds = foldr (\(v,a) e -> (v, trans e a) : e) env ds
  -- Important to fold from the right, since earlier definitions may depend on later ones

