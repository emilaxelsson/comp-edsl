{-# LANGUAGE ImplicitParams #-}

-- | Attribute grammars

-- TODO This module will be implemented in compdata

module EDSL.AG
    ( module Data.Comp.Automata
    , Syn'
    , Syn
    , prodSyn'
    , prodSyn
    , (|*|)
    , Inh'
    , Inh
    , prodInh
    , (>*<)
    , runAG
    , runAG'
    , Rewrite
    , runRewrite
    , runAGAnn
    , RewriteDeep
    , runRewriteDeep
    ) where



import Data.Map (Map)
import qualified Data.Map as Map

import Data.Comp
import Data.Comp.Automata ((:<) (..), above, below, (|->), (&), o)
import Data.Comp.Number



explicit :: ((?above :: q, ?below :: a -> q) => b) -> q -> (a -> q) -> b
explicit x ab be = x
  where
    ?above = ab
    ?below = be

type Syn' f p q = forall a . (?below :: a -> p, ?above :: p) => f a -> q
type Syn  f p q = (q :< p) => Syn' f p q

prodSyn :: (p :< c, q :< c) => Syn f c p -> Syn f c q -> Syn f c (p,q)
prodSyn sp sq t = (sp t, sq t)

prodSyn' :: Syn' f c p -> Syn' f c q -> Syn' f c (p,q)
prodSyn' sp sq t = (sp t, sq t)

(|*|) :: (p :< c, q :< c) => Syn f c p -> Syn f c q -> Syn f c (p,q)
(|*|) = prodSyn

type Inh' f p q = forall i . (Ord i, ?below :: i -> p, ?above :: p) => f i -> Map i q
type Inh  f p q = (q :< p) => Inh' f p q

data ProdState p q
    = LState p
     | RState q
     | BState p q

prodMap :: (Ord i) => p -> q -> Map i p -> Map i q -> Map i (p,q)
prodMap p q mp mq = Map.map final $ Map.unionWith combine ps qs
  where
    ps = Map.map LState mp
    qs = Map.map RState mq
    combine (LState p) (RState q) = BState p q
    combine (RState q) (LState p) = BState p q
    combine _ _                   = error "unexpected merging"
    final (LState p) = (p, q)
    final (RState q) = (p, q)
    final (BState p q) = (p,q)

prodInh :: (p :< c, q :< c) => Inh f c p -> Inh f c q -> Inh f c (p,q)
prodInh sp sq t = prodMap above above (sp t) (sq t)

(>*<) :: (p :< c, q :< c, Functor f) => Inh f c p -> Inh f c q -> Inh f c (p,q)
(>*<) = prodInh

runAG :: Traversable f => Syn' f (u,d) u -> Inh' f (u,d) d -> d -> Term f -> u
runAG up down d (Term t) = u
  where
    t' = fmap bel $ number t
    bel (Numbered (i,s)) = Numbered (i,(runAG up down d' s, d'))
      where d' = Map.findWithDefault d (Numbered (i,undefined)) m
    m = explicit down (u,d) unNumbered t'
    u = explicit up (u,d) unNumbered t'

runAG' :: Traversable f => Syn f (u,d) u -> Inh f (u,d) d -> d -> Term f -> u
runAG' up down d (Term t) = u
  where
    t' = fmap bel $ number t
    bel (Numbered (i,s)) = Numbered (i,(runAG up down d' s, d'))
      where d' = Map.findWithDefault d (Numbered (i,undefined)) m
    m = explicit down (u,d) unNumbered t'
    u = explicit up (u,d) unNumbered t'

type Rewrite f q g = forall a . (?below :: a -> q, ?above :: q) => f a -> Context g a

runRewrite
    :: (Traversable f, Functor g)
    => Syn' f (u,d) u
    -> Inh' f (u,d) d
    -> Rewrite f (u,d) g
    -> d
    -> Term f
    -> (u, Term g)
runRewrite up down trans d (Term t) = (u,t'')
  where
    t'  = fmap bel $ number t
    m   = explicit down (u,d) (fst . unNumbered) t'
    u   = explicit up (u,d) (fst . unNumbered) t'
    t'' = appCxt $ fmap (snd . unNumbered) $ explicit trans (u,d) (fst . unNumbered) t'
    bel (Numbered (i,s)) =
        let d' = Map.findWithDefault d (Numbered (i,undefined)) m
            (u',s') = runRewrite up down trans d' s
        in Numbered (i,((u',d'),s'))

runAGAnn :: Traversable f
    => Syn' f (u,d) u
    -> Inh' f (u,d) d
    -> d
    -> Term f
    -> Term (f :&: (u,d))
runAGAnn up down d = snd . runRewrite up down rew d
  where
    rew f = simpCxt (f :&: ?above)

type RewriteDeep f q g = forall a . (?below :: a -> q, ?above :: q, ?match :: a -> f a) =>
    f a -> Context g a

getAnn :: Term (f :&: a) -> a
getAnn (Term (_ :&: a)) = a

dropAnn :: Term (f :&: a) -> f (Term (f :&: a))
dropAnn (Term (f :&: _)) = f

runRewriteDeep :: forall f g u d . (Traversable f, Functor g, Traversable g)
    => Syn'        f (u,d) u
    -> Inh'        f (u,d) d
    -> RewriteDeep f (u,d) g
    -> d
    -> Term f
    -> (u, Term g)
runRewriteDeep up down trans d t = (fst (getAnn t'), rew t')
  where
    t' = runAGAnn up down d t

    rew :: Term (f :&: (u,d)) -> Term g
    rew (Term (f :&: (u,d))) = appCxt $ fmap rew f'
      where
        f' = let ?match = dropAnn in explicit trans (u,d) getAnn f

