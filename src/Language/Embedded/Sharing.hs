-- | Utilities for working with abstract syntax graphs
--
-- An abstract syntax graph ('DAG') is essentially an AST with 'Let' binders; however, instead of
-- 'Let', this module uses a functor transformer 'Where' that allows attaching a number of local
-- definitions to each node in an AST.
--
-- The functions 'dagToTerm' and 'termToDAG' go back and forth between terms with 'Where' and 'Let'
-- for local binders.
--
-- It is often desired to ignore the sharing structure when transforming 'DAG's. The sharing
-- structure is then only there to give a compact representation, and should not affect the
-- semantics of the term. Such transformations can be written using 'expose', which looks through
-- the sharing structure and exposes the top-most constructor for pattern matching.

module Language.Embedded.Sharing where



import Data.Comp

import Language.Embedded.Constructs



-- | A 'DAG' is a term where each node may include a number of local definitions. These definitions
-- mean the same thing as introducing a sequence of 'Let' nodes (see 'dagToTerm').
type DAG f = Term (Where f)

-- | Pair a functor with a 'Defs' list
data Where f a = Where { whereDefs :: Defs f, whereBody :: f a }
  deriving (Functor)

-- | A sequence of local definitions. Earlier definitions may depend on later ones, and earlier
-- definitions shadow later ones.
type Defs f = [(Name, DAG f)]

instance EqF f => EqF (Where f)
  where
    eqF (Where ds1 f1) (Where ds2 f2) = ds1==ds2 && eqF f1 f2

-- | Methods for querying a functor that may be a 'Var' or a 'Lam'
data BindDict f = BindDict
    { isVar :: forall a . f a -> Maybe Name
    , isLam :: forall a . f a -> Maybe (Name,a)
    }

-- | Default 'BindDict' implementation
bindDictDefault :: (Binding :<: f) => BindDict f
bindDictDefault = BindDict
    { isVar = \f -> do
        Var v <- proj f
        return v
    , isLam = \f -> do
        Lam v a <- proj f
        return (v,a)
    }

-- | 'BindDict' for annotated functors
bindDictAnn :: BindDict f -> BindDict (f :&: a)
bindDictAnn bd = BindDict
    { isVar = \(f :&: _) -> do
        v <- isVar bd f
        return v
    , isLam = \(f :&: _) -> do
        (v,a) <- isLam bd f
        return (v,a)
    }

-- | Convert a 'Defs' list to a chain of let bindings
defsToTerm :: (Binding :<: f, Let :<: f, Functor f) => Defs f -> Term f -> Term f
defsToTerm []           f = f
defsToTerm ((v,dag):ds) f = defsToTerm ds $ inject $ Let (dagToTerm dag) $ inject $ Lam v f

-- | Defines the meaning of 'DAG' by converting it to a tree with let bindings
dagToTerm :: (Binding :<: f, Let :<: f, Functor f) => DAG f -> Term f
dagToTerm (Term (Where ds f)) = defsToTerm ds $ Term $ fmap dagToTerm f

-- | Add definitions to the root in a 'DAG'. The existing definitions shadow and may depend on the
-- new ones.
addDefs :: Defs f -> DAG f -> DAG f
addDefs ds (Term (Where ds' f)) = Term (Where (ds' ++ ds) f)  -- `ds'` shadows `ds`

-- | Convert a 'Term' with let bindings to a 'DAG'. The result does not have any 'Let' bindings even
-- though the type does not enforce this.
termToDAG :: (Binding :<: f, Let :<: f, Functor f) => Term f -> DAG f
termToDAG t
    | Just (v,a,b) <- viewLet t
    = addDefs [(v, termToDAG a)] $ termToDAG b
termToDAG (Term f) = Term $ Where [] $ fmap termToDAG f

-- | 'dagToTerm' is the inverse of 'termToDAG'. The converse only holds if the original 'DAG' does
-- not have any 'Let' nodes (i.e. all bindings are represented using 'Where').
prop_DAG :: (Binding :<: f, Let :<: f, Functor f, EqF f) => Term f -> Bool
prop_DAG t = dagToTerm (termToDAG t) == t

-- | Fold a term by treating sharing transparently. The semantics is as if all sharing is inlined,
-- but the implementation avoids duplication.
foldWithLet :: (Binding :<: f, Let :<: f, Functor f) => (f a -> a) -> Term f -> a
foldWithLet alg = go []
  where
    go env t
      | Just (Var v) <- project t
      , Just a       <- lookup v env
      = a
    go env t
      | Just (v,a,b) <- viewLet t
      = go ((v, go env a) : env) b
    go env (Term f) = alg $ fmap (go env) f

-- | Fold a 'DAG' by treating sharing transparently. The semantics is as if all sharing is inlined,
-- but the implementation avoids duplication.
foldDAG :: (Binding :<: f, Let :<: f, Functor f) => (f a -> a) -> DAG f -> a
foldDAG alg = foldWithLet alg . dagToTerm

-- | Inline all 'Let' bindings. Corresponds to call by name reduction.
inlineLet :: (Binding :<: f, Let :<: f, Functor f) => Term f -> Term f
inlineLet = foldWithLet Term

-- | Inline all 'Where' definitions and 'Let' bindings. Corresponds to call by name reduction.
inlineDAG :: (Binding :<: f, Let :<: f, Functor f) => DAG f -> Term f
inlineDAG = foldWithLet Term . dagToTerm

-- | 'foldWithLet' has the same behavior as 'cata' composed with 'inlineLet'
prop_foldWithLet :: (Binding :<: f, Let :<: f, Functor f, Eq a) => (f a -> a) -> Term f -> Bool
prop_foldWithLet alg t = foldWithLet alg t == cata alg (inlineLet t)

-- | Expose the top-most constructor in a 'DAG' given an environment of definitions in scope.
--
-- * If the top-most node is a variable that has a definition in scope (either in the environment or
--   in the local 'Defs' attached to the node), this definition is returned and 'expose'd.
--
-- * Otherwise, the local definitions of the node are distributed down to the children, which
--   ensures that the (call by name) semantics of the 'DAG' is not affected.
expose :: Functor f => BindDict f -> Defs f -> DAG f -> f (DAG f)
expose bd env (Term (Where ds f))
    | Just v <- isVar bd f
    , let ds' = dropWhile ((v /=) . fst) ds  -- Strip irrelevant bindings from `ds`
    , Just t <- lookup v (ds' ++ env)        -- `ds` shadows `env`
    , let ds'' = drop 1 ds'                  -- The part of `ds` that `t` may depend on
    = expose bd env $ addDefs ds'' t
expose bd env (Term (Where ds f)) = fmap (addDefs ds) f

getAnn :: (f :&: a) b -> a
getAnn (f :&: a) = a

dropAnn :: (f :&: a) b -> f b
dropAnn (f :&: a) = f

-- | Use a 'DAG' transformer to transform a 'Defs' list
transDefs
    :: (Defs g -> DAG f  -> DAG g)
    -> (Defs g -> Defs f -> Defs g)
transDefs trans env ds = foldr (\(v,a) e -> (v, trans e a) : e) env ds
  -- Important to fold from the right, since earlier definitions may depend on later ones

stripAnnDAG :: Functor f => DAG (f :&: a) -> DAG f
stripAnnDAG = cata (\(Where ds (f :&: _)) -> Term (Where [(v, stripAnnDAG a) | (v,a) <- ds] f))

alphaEqDAG :: (EqF f, Functor f) => DAG (f :&: a) -> DAG (f :&: a) -> Bool
alphaEqDAG a b = stripAnnDAG a == stripAnnDAG b
  -- TODO Use alpha equivalence
