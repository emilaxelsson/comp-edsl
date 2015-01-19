-- | Utilities for working with abstract syntax trees with \"transparent\" sharing
--
-- The type 'DAG' represents ASTs with sharing. It is essentially a normal term with let binders.
-- But instead of using 'Let', this module uses a functor transformer 'DAGF' that allows adds a
-- special kind of let binding 'DLet' and a corresponding variable 'DVar' constructor.
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



-- | 'DAG' variable name
newtype DName = DName Integer
  deriving (Eq, Ord, Num, Enum, Real, Integral)

instance Show DName
  where
    show (DName n) = show n

toDName :: Name -> DName
toDName (Name n) = DName n

fromDName :: DName -> Name
fromDName (DName n) = Name n

-- | Environment for let-bound variables
type DAGEnv a = [(DName,a)]
  -- TODO Use a map

-- | Extend a base functor with variables and let bindings
data DAGF f a
    = DVar DName
    | DLet DName a a
    | DIn (f a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance EqF f => EqF (DAGF f)
  where
    eqF (DVar v1)       (DVar v2)       = v1==v2
    eqF (DLet v1 a1 b1) (DLet v2 a2 b2) = v1==v2 && a1==a2 && b1==b2
    eqF (DIn f1)        (DIn f2)        = eqF f1 f2
    eqF _ _ = False

instance ShowF f => ShowF (DAGF f)
  where
    showF (DVar v)     = "dv" ++ show v
    showF (DLet v a b) = "(DLet " ++ unwords [show v, a, b] ++ ")"
    showF (DIn f)      = showF f

instance (f :<<: g) => f :<<: DAGF g
  where
    prjInj (DIn g) = do
        (f, back) <- prjInj g
        return (f, DIn . back)
    prjInj _ = Nothing

-- | Terms with sharing
type DAG f = Term (DAGF f)

-- | Fold a 'DAG' without exposing the sharing structure. The semantics is as if all bindings were
-- inlined, but the implementation only visits each node in the 'DAG' once. The 'DAG' is assumed not
-- to have any free 'DVar'.
--
-- It is probably not a good idea to use 'foldDAG' to transform terms, since the substitution of
-- shared terms does not deal with capturing (only a problem when there are other binders than `Let`
-- in the term). E.g. @`foldDAG` `Term`@ will inline all shared terms, but will generally not
-- preserve the semantics.
foldDAG :: Functor f => (f a -> a) -> DAG f -> a
foldDAG alg = go []
  where
    go env (Term (DVar v))     = fromJust $ lookup v env
    go env (Term (DLet v a b)) = go ((v, go env a) : env) b
    go env (Term (DIn f))      = alg $ fmap (go env) f

type Renaming = [(Name,Name)]

-- | Return an unused name given a list of used names
unusedName :: [Name] -> Name
unusedName [] = 0
unusedName ns = maximum ns + 1

inlineDAGEnv :: (Binding :<<: f, Functor f) => DAGEnv (Term f) -> Renaming -> DAG f -> Term f
inlineDAGEnv env re (Term (DVar v)) = fromJust $ lookup v env
inlineDAGEnv env re (Term (DLet v a b)) = inlineDAGEnv ((v, inlineDAGEnv env re a) : env) re b
inlineDAGEnv env re (Term (DIn f))
    | Just (Var v, back) <- prjInj f
    , Just v'            <- lookup v re
    = Term $ back $ Var v'
inlineDAGEnv env re (Term (DIn f))
    | Just (Lam v a, back) <- prjInj f
    , let v'' = unusedName [v' | (_,v') <- re]
    , let re' = (v,v'') : re
    = Term $ back $ Lam v'' $ inlineDAGEnv env re' a
inlineDAGEnv env re (Term (DIn f)) = Term $ fmap (inlineDAGEnv env re) f

-- | Capture-avoiding inlining of all let bindings
--
-- Uses the "rapier" method described in "Secrets of the Glasgow Haskell Compiler inliner" (Peyton
-- Jones and Marlow, JFP 2006) to rename variables where there's risk for capturing.
inlineDAG :: (Binding :<<: f, Functor f, Foldable f) => DAG f -> Term f
inlineDAG t = inlineDAGEnv [] init t
  where
    init = case Set.toList $ freeVars t of
      [] -> []
      vs -> let v = maximum vs in [(v,v)]
        -- Insert the highest free variable in the initial renaming to make sure that fresh names
        -- are not already used as free variables

-- | A sequence of local definitions. Earlier definitions may depend on later ones, and earlier
-- definitions shadow later ones.
type Defs f = [(DName, DAG f)]

-- | Add a number of local binders to a term. Existing binders shadow and may depend on the new
-- ones. @`uncurry` `addDefs`@ is the left inverse of 'splitDefs'.
addDefs :: Functor f => Defs f -> DAG f -> DAG f
addDefs []         t = t
addDefs ((v,a):ds) t = addDefs ds $ Term $ DLet v a t

-- | Gather all let bindings at the root of a term. The result is the local definitions and the
-- first non-let node. @`uncurry` `addDefs`@ is the left inverse of this function.
splitDefs :: Functor f => DAG f -> (Defs f, DAG f)
splitDefs = go []
  where
    go ds (Term (DLet v a b)) = go ((v,a):ds) b
    go ds t                   = (ds,t)

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
-- variables.
expose :: Traversable f => Defs f -> DAG f -> f (DAG f)
expose env t
    | DVar v <- f
    , let ds'  = dropWhile ((v /=) . fst) ds  -- Strip irrelevant bindings from `ds`
    , Just t  <- lookup v (ds' ++ env)        -- `ds` shadows `env`
    , let ds'' = drop 1 ds'                   -- The part of `ds` that `t` may depend on
    = expose env $ addDefs ds'' t
        -- TODO This is a bit inefficient because `expose` will immediately apply `splitDefs`
    | DIn g <- f
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

