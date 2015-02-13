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



import qualified Data.Foldable as Foldable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)

import Data.Comp.Ops

import Language.Embedded hiding (Typeable)



-- | Name of a 'DAG' reference
newtype RName = RName Integer
  deriving (Eq, Ord, Num, Enum, Real, Integral, Typeable)

instance Show RName
  where
    show (RName n) = show n

toRName :: Name -> RName
toRName (Name n) = RName n

fromRName :: RName -> Name
fromRName (RName n) = Name n

-- | Variables and bindings in a 'DAG'
data DAGF a
    = Ref RName
    | Def RName a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF,makeOrdF,makeShowF,makeShowConstr] [''DAGF]

-- | Terms with sharing
type DAG f = Term (DAGF :+: f)

-- | Find the set of free references in a 'DAG'
freeRefs :: (Functor f, Foldable f) => DAG f -> Set RName
freeRefs (Term (Inl (Ref v)))     = Set.singleton v
freeRefs (Term (Inl (Def v a b))) = Set.union (freeRefs a) $ Set.delete v $ freeRefs b
freeRefs (Term f)                 = Foldable.fold $ fmap freeRefs f

-- | Fold a 'DAG' without exposing the sharing structure. The semantics is as if all bindings were
-- inlined, but the implementation only visits each node in the 'DAG' once. The 'DAG' is assumed not
-- to have any free 'Ref'.
--
-- It is probably not a good idea to use 'foldDAG' to transform terms, since the substitution of
-- shared terms does not deal with capturing (only a problem when there are other binders than `Def`
-- in the term). E.g. @`foldDAG` `Term`@ will inline all shared terms, but will generally not
-- preserve the semantics.
foldDAG :: Functor f => (f a -> a) -> DAG f -> a
foldDAG alg = go Map.empty
  where
    go env (Term (Inl (Ref v)))
      | Just a <- Map.lookup v env  = a
    go env (Term (Inl (Def v a b))) = go (Map.insert v (go env a) env) b
    go env (Term (Inr f))           = alg $ fmap (go env) f

type Renaming = [(Name,Name)]

-- | Return an unused name given a list of used names
unusedName :: [Name] -> Name
unusedName [] = 0
unusedName ns = maximum ns + 1

inlineDAGEnv :: (Binding :<<: f, Functor f) => Map RName (Term f) -> Map Name Name -> DAG f -> Term f
inlineDAGEnv env re (Term (Inl (Ref v)))
    | Just a <- Map.lookup v env = a
inlineDAGEnv env re (Term (Inl (Def v a b))) =
    inlineDAGEnv (Map.insert v (inlineDAGEnv env re a) env) re b
inlineDAGEnv env re (Term (Inr f))
    | Just (Var v, back) <- prjInj f
    , Just v'            <- Map.lookup v re
    = Term $ back $ Var v'
inlineDAGEnv env re (Term (Inr f))
    | Just (Lam v a, back) <- prjInj f
    , let v'  = unusedName [w | (_,w) <- Map.toList re]
    , let re' = Map.insert v v' re
    = Term $ back $ Lam v' $ inlineDAGEnv env re' a
inlineDAGEnv env re (Term (Inr f)) = Term $ fmap (inlineDAGEnv env re) f

-- | Capture-avoiding inlining of all 'Def' bindings
--
-- Uses the "rapier" method described in "Secrets of the Glasgow Haskell Compiler inliner" (Peyton
-- Jones and Marlow, JFP 2006) to rename variables where there's risk for capturing.
inlineDAG :: (Binding :<<: f, Functor f, Foldable f) => DAG f -> Term f
inlineDAG t = inlineDAGEnv Map.empty (Map.fromList init) t
  where
    init = case Set.toList $ freeVars t of
      [] -> []
      vs -> let v = maximum vs in [(v,v)]
        -- Insert the highest free variable in the initial renaming to make sure that fresh names
        -- are not already used as free variables

-- | A sequence of local definitions. Earlier definitions may depend on later ones, and earlier
-- definitions shadow later ones.
type Defs f = [(RName, DAG f)]

-- | Add a number of local binders to a term. Existing binders shadow and may depend on the new
-- ones. @`uncurry` `addDefs`@ is the left inverse of 'splitDefs'.
addDefs :: Functor f => Defs f -> DAG f -> DAG f
addDefs []         t = t
addDefs ((v,a):ds) t = addDefs ds $ Term $ Inl $ Def v a t

-- | Gather all 'Def' bindings at the root of a term. The result is the local definitions and the
-- first non-'Def' node. @`uncurry` `addDefs`@ is the left inverse of this function.
splitDefs :: Functor f => DAG f -> (Defs f, DAG f)
splitDefs = go []
  where
    go ds (Term (Inl (Def v a b))) = go ((v,a):ds) b
    go ds t = (ds,t)

freeVarsDefs :: (Binding :<<: f, Functor f, Foldable f) => Defs f -> Set Name
freeVarsDefs = Set.unions . map (freeVars . snd)

-- | Expose the top-most constructor in a 'DAG' given an environment of definitions in scope. It
-- works roughly as follows:
--
-- * 'Def' binders at the top are removed and gathered in a list of local definitions.
--
-- * If the top-most node (after removing local definitions) is a 'Ref' variable, its unfolding
--   (coming either in the environment or from the local definitions) is returned and 'expose'd.
--
-- * Otherwise, the local definitions of the node are distributed down to the children, which
--   ensures that the (call-by-name) semantics of the 'DAG' is not affected.
--
-- When calling @`expose` env t@, it is assumed that @`addDefs` env t@ does not have any free 'Ref'
-- variables. It is also assumed that all definitions in `env` have unique names (i.e. that
-- @map fst env@ has no duplicates).
expose :: (Binding :<<: f, Traversable f) => Defs f -> DAG f -> f (DAG f)
expose env t
    | Inl (Ref v) <- f
    , Just t' <- lookup v (ds ++ env)  -- `ds` shadows `env`
    , let ds' = drop 1 $ dropWhile ((v /=) . fst) ds  -- The part of `ds` that `t'` may depend on
    = expose env $ addDefs ds' t'
        -- TODO This is a bit inefficient because `expose` will immediately apply `splitDefs`

    | Inr g <- f
    , Just (Lam v a, back) <- prjInj g
    , let w = unusedName $ Set.toList $ allVars a `Set.union` freeVarsDefs (ds ++ env)
    = back $ Lam w $ addDefs ds $ rename v w a

    | Inr g <- f = fmap (addDefs ds) g
        -- `splitDefs` cannot return `Def`, so we don't need to handle that case
  where
    (ds, Term f) = splitDefs t

-- In the `Ref` case, it is important to throw away the first part of `ds` because otherwise those
-- bindings can capture variables in `t'`. (If `v` is found in `env` rather than in `ds`, there
-- could also be definitions in the first part of `env` that capture variables in `t'`, but this
-- won't happen due to the assumption that `env` has unique identifiers (and this is the reason why
-- we need that assumption).)

-- Note that there are two worrying inefficiencies in `expose`:
--
--   * Finding the variables in `a` and `ds ++ env`
--   * Renaming `v` to `w` in `a`
--
-- For the first one, the solution would be to cache the set of free variables in `DAG`s. For this
-- to work, one would have to hide `DAG` node creation behind a safe interface that correctly sets
-- the set of variables.
--
-- The second one is harder. If DAG references and variables had the same name space, it would be
-- possible to do the renaming by just introducing a `Ref`. But because of the separate name spaces,
-- one would have to use a different construct for renaming. Using `Let` is not a good idea, because
-- one would then have to construct a new variable, which requires a `Binding :<: f` constraint.
-- Another problem is that since `expose` does not handle `Let` nodes the way it handles `Def`,
-- those `Let` nodes might appear in the result of `expose` (e.g. if we have a deep pattern that
-- first exposes a lambda and then its body).

-- | Use a 'DAG' transformer to transform a 'Defs' list
transDefs
    :: (Defs g -> DAG f  -> DAG g)
    -> (Defs g -> Defs f -> Defs g)
transDefs trans env ds = foldr (\(v,a) e -> (v, trans e a) : e) env ds
  -- Important to fold from the right, since earlier definitions may depend on later ones

