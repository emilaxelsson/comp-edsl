{-# LANGUAGE TemplateHaskell #-}

-- | Utilities for working with abstract syntax trees with \"transparent\" sharing
--
-- The type 'DAG' represents ASTs with sharing. It is a term with an extra form of let binding,
-- called 'Def' and separate variables for referring to those bindings.
--
-- It is sometimes desired to ignore the sharing structure when traversing or transforming 'DAG's.
-- The sharing structure is then only there to give a compact representation, and should not affect
-- the semantics of the traversal or transformation. The functions 'foldDAG' and 'expose' support
-- this kind of programming by dealing with sharing under the hood.

module Language.Embedded.Sharing where



import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Comp.Ops

import Language.Embedded



-- | Variables and bindings in a 'DAG'
data DAGF a
    = DVar Name
    | DLet Name a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF,makeOrdF,makeShowF,makeShowConstr] [''DAGF]

-- | Terms with sharing
type DAG f = Term (DAGF :+: f)

-- | Fold a 'DAG' without exposing the sharing structure. The semantics is as if all bindings were
-- inlined, but the implementation only visits each node in the 'DAG' once. The 'DAG' is assumed not
-- to have any free 'DVar'.
--
-- It is probably not a good idea to use 'foldDAG' to transform terms, since the substitution of
-- shared terms does not deal with capturing (only a problem when there are other binders than `Let`
-- in the term). E.g. @`foldDAG` `Term`@ will inline all shared terms, but will generally not
-- preserve the semantics.
foldDAG :: Functor f => (f a -> a) -> DAG f -> a
foldDAG alg = go emptyEnv
  where
    go env (Term (Inl (DVar v)))
      | Just a <- lookEnv v env      = a
    go env (Term (Inl (DLet v a b))) = go ((v, go env a) |> env) b
    go env (Term (Inr f))            = alg $ fmap (go env) f

type Renaming = [(Name,Name)]

-- | Return an unused name given a list of used names
unusedName :: [Name] -> Name
unusedName [] = 0
unusedName ns = maximum ns + 1

inlineDAGEnv :: (Binding :<<: f, Functor f) => Env (Term f) -> Env Name -> DAG f -> Term f
inlineDAGEnv env re (Term (Inl (DVar v)))
    | Just a <- lookEnv v env = a
inlineDAGEnv env re (Term (Inl (DLet v a b))) =
    inlineDAGEnv ((v, inlineDAGEnv env re a) |> env) re b
inlineDAGEnv env re (Term (Inr f))
    | Just (Var v, back) <- prjInj f
    , Just v'            <- lookEnv v re
    = Term $ back $ Var v'
inlineDAGEnv env re (Term (Inr f))
    | Just (Lam v a, back) <- prjInj f
    , let v'  = unusedName [w | (_,w) <- toListEnv re]
    , let re' = (v,v') |> re
    = Term $ back $ Lam v' $ inlineDAGEnv env re' a
inlineDAGEnv env re (Term (Inr f)) = Term $ fmap (inlineDAGEnv env re) f

-- | Capture-avoiding inlining of all let bindings
--
-- Uses the "rapier" method described in "Secrets of the Glasgow Haskell Compiler inliner" (Peyton
-- Jones and Marlow, JFP 2006) to rename variables where there's risk for capturing.
inlineDAG :: (Binding :<<: f, Functor f, Foldable f) => DAG f -> Term f
inlineDAG t = inlineDAGEnv emptyEnv (fromListEnv init) t
  where
    init = case Set.toList $ freeVars t of
      [] -> []
      vs -> let v = maximum vs in [(v,v)]
        -- Insert the highest free variable in the initial renaming to make sure that fresh names
        -- are not already used as free variables

-- | A sequence of local definitions. Earlier definitions may depend on later ones, and earlier
-- definitions shadow later ones.
type Defs f = [(Name, DAG f)]

-- | Add a number of local binders to a term. Existing binders shadow and may depend on the new
-- ones. @`uncurry` `addDefs`@ is the left inverse of 'splitDefs'.
addDefs :: Functor f => Defs f -> DAG f -> DAG f
addDefs []         t = t
addDefs ((v,a):ds) t = addDefs ds $ Term $ Inl $ DLet v a t

-- | Gather all let bindings at the root of a term. The result is the local definitions and the
-- first non-let node. @`uncurry` `addDefs`@ is the left inverse of this function.
splitDefs :: Functor f => DAG f -> (Defs f, DAG f)
splitDefs = go []
  where
    go ds (Term (Inl (DLet v a b))) = go ((v,a):ds) b
    go ds t = (ds,t)

-- | Expose the top-most constructor in a 'DAG' given an environment of definitions in scope. It
-- works roughly as follows:
--
-- * 'DLet' binders at the top are removed and gathered in a list of local definitions.
--
-- * If the top-most node (after removing local definitions) is a 'DVar' variable, its unfolding
--   (coming either in the environment or from the local definitions) is returned and 'expose'd.
--
-- * Otherwise, the local definitions of the node are distributed down to the children, which
--   ensures that the (call-by-name) semantics of the 'DAG' is not affected.
--
-- When calling @`expose` env t@, it is assumed that @`addDefs` env t@ does not have any free 'DVar'
-- variables. It is also assumed that all definitions in `env` have unique names (i.e. that
-- @map fst env@ has no duplicates).
expose :: (Binding :<<: f, Traversable f) => [Name] -> Defs f -> DAG f -> f (DAG f)
expose ns env t
    | Inl (DVar v) <- f
    , Just t' <- lookup v (ds ++ env)  -- `ds` shadows `env`
    , let ds' = drop 1 $ dropWhile ((v /=) . fst) ds  -- The part of `ds` that `t'` may depend on
        -- It is important to throw away the first part of `ds` because otherwise those bindings can
        -- capture variables in `t'`. (If `v` is found in `env` rather than in `ds`, there could
        -- also be definitions in the first part of `env` that capture variables in `t'`, but this
        -- won't happen due to the assumption that `env` has unique identifiers (and this is the
        -- reason why we need that assumption).)
    = expose ns env $ addDefs ds' t'
        -- TODO This is a bit inefficient because `expose` will immediately apply `splitDefs`
    | Inr g <- f
    , Just (Lam v a, back) <- prjInj g
    , let w = unusedName $ (v:) $ (ns++) $ Set.toList $ usedVars a
    = back $ Lam w $ addDefs ds $ rename v w a
    | Inr g <- f
    = fmap (addDefs ds) g
        -- `splitDefs` cannot return `DLet`, so we don't need to handle that case
  where
    (ds, Term f) = splitDefs t

-- | Use a 'DAG' transformer to transform a 'Defs' list
transDefs
    :: (Defs g -> DAG f  -> DAG g)
    -> (Defs g -> Defs f -> Defs g)
transDefs trans env ds = foldr (\(v,a) e -> (v, trans e a) : e) env ds
  -- Important to fold from the right, since earlier definitions may depend on later ones

