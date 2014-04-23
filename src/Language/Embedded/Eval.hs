{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Attribute grammars for constructing semantic trees

module Language.Embedded.Eval where



import Data.Syntactic (AST (..), (:&:) (..), E (..), EF (..))
import qualified Data.Syntactic as S
import Data.Syntactic.TypeUniverse
import Data.Syntactic.Evaluation

import Language.Embedded.Syntax
import Language.Embedded.AG
import Language.Embedded.Constructs



-- | Semantic tree attribute
newtype SemTree t = SemTree { unSemTree :: Maybe (EF (AST (Sem t) :&: TypeRep t)) }

-- | Get the 'SemTree' attribute
semOf :: (?below :: a -> q, SemTree t :< q) => a -> Maybe (EF (AST (Sem t) :&: TypeRep t))
semOf = unSemTree . below

-- | Get the 'SemTree' attribute; fix the type variable by a 'Proxy'
semOfT :: (?below :: a -> q, SemTree t :< q) =>
    Proxy t -> a -> Maybe (EF (AST (Sem t) :&: TypeRep t))
semOfT _ = unSemTree . below

-- | Get the type of a 'SemTree' attribute
typeOf :: (?below :: a -> q, SemTree t :< q) => a -> EF (TR t)
typeOf a = case semOf a of
    Just (EF (_ :&: TypeRep t)) -> EF t

-- | Attribute grammar for constructing semantic trees
class SemTreeAG f t
  where
    -- | Synthesize the 'SemTree' attribute
    semTreeS :: (Env (EF (TR t)) :< atts) => Syn f atts (SemTree t)

    -- | Compute the inherited type environment for constructing a semantic tree
    semTreeI :: (SemTree t :< atts, Args :< atts) => Inh f atts (Env (EF (TR t)))
    semTreeI _ = o

-- | Construct a semantic tree from a term
semTree :: forall f t
    .  ( SemTreeAG f t
       , Traversable f
       , Binding :<: f
       )
    => [(Name, EF (TR t))]
    -> Term f
    -> Maybe (EF (AST (Sem t) :&: TypeRep t))
semTree env = unSemTree . fst . runAG (semTreeS |*| argsS) semTreeI' (Env env)
  where
    semTreeI' :: Inh' f ((SemTree t, Args), Env (EF (TR t))) (Env (EF (TR t)))
    semTreeI' = semTreeI
      -- Why needed?

-- | Evaluate a term using a semantic tree
evalTop :: forall f t a
    .  ( Typeable t a
       , SemTreeAG f t
       , Traversable f
       , Binding :<: f
       , FunType S.:<: t
       , TypeEq t t
       )
    => Proxy t -> Term f -> a
evalTop _ e = go e typeRep []
  where
    go :: Term f -> TypeRep t b -> EvalEnv t -> b
    go e t env  -- This case handles top-level lambdas
        | Just (Lam v b) <- project e
        , [E ta, E tb]   <- matchCon t
        , Just Dict      <- typeEq t (funType ta tb)
        = \a -> go b tb ((v, Dyn ta a) : env)
    go e te env
        | Just (EF (s :&: t)) <- semTree env' e
        , Just Dict           <- typeEq t te
        = evalSem env s
      where
        env' = [(v, EF t) | (v, Dyn (TypeRep t) _) <- env]

-- | General implementation of 'semTreeS' for construct of type @A -> B@
semTreeS_A_A :: forall t atts q a b
    .  ( TypeEq t t
       , ?below :: atts -> q
       , SemTree t :< q
       , Typeable t a
       , Typeable t b
       )
    => (a -> b) -> atts -> SemTree t
semTreeS_A_A f a = SemTree $ do
    EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
    Dict <- typeEq ta (typeRep :: TypeRep t a)
    return $ EF $ (Sym (Sem f) :$ a') :&: typeRep

-- | General implementation of 'semTreeS' for construct of type @A -> B -> C@
semTreeS_A_A_A :: forall t atts q a b c
    .  ( TypeEq t t
       , ?below :: atts -> q
       , SemTree t :< q
       , Typeable t a
       , Typeable t b
       , Typeable t c
       )
    => (a -> b -> c) -> atts -> atts -> SemTree t
semTreeS_A_A_A f a b = SemTree $ do
    EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
    EF (b' :&: tb) <- semOfT (Proxy :: Proxy t) b
    Dict <- typeEq ta (typeRep :: TypeRep t a)
    Dict <- typeEq tb (typeRep :: TypeRep t b)
    return $ EF $ (Sym (Sem f) :$ a' :$ b') :&: typeRep

-- | General implementation of 'semTreeS' for construct of type @p a => a -> a@
semTreeS_a_a :: forall t p a q
    .  ( TypeEq t t
       , PWitness p t t
       , ?below :: a -> q
       , SemTree t :< q
       )
    => Proxy p -> (forall a . p a => a -> a) -> a -> SemTree t
semTreeS_a_a p f a = SemTree $ do
    EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
    Dict <- pwit p ta
    return $ EF $ (Sym (Sem f) :$ a') :&: ta

-- | General implementation of 'semTreeS' for construct of type @p a => a -> a -> a@
semTreeS_a_a_a :: forall t p a q
    .  ( TypeEq t t
       , PWitness p t t
       , ?below :: a -> q
       , SemTree t :< q
       )
    => Proxy p -> (forall a . p a => a -> a -> a) -> a -> a -> SemTree t
semTreeS_a_a_a p f a b = SemTree $ do
    EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
    EF (b' :&: tb) <- semOfT (Proxy :: Proxy t) b
    Dict <- pwit p ta
    Dict <- typeEq ta tb
    return $ EF $ (Sym (Sem f) :$ a' :$ b') :&: ta

-- | General implementation of 'semTreeS' for construct of type @p a => a -> B@
semTreeS_a_a_B :: forall t p atts q a b
    .  ( TypeEq t t
       , PWitness p t t
       , ?below :: atts -> q
       , SemTree t :< q
       , Typeable t b
       )
    => Proxy p -> (forall a . p a => a -> a -> b) -> atts -> atts -> SemTree t
semTreeS_a_a_B p f a b = SemTree $ do
    EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
    EF (b' :&: tb) <- semOfT (Proxy :: Proxy t) b
    Dict <- pwit p ta
    Dict <- typeEq ta tb
    return $ EF $ (Sym (Sem f) :$ a' :$ b') :&: typeRep

instance (SemTreeAG f t, SemTreeAG g t) => SemTreeAG (f :+: g) t
  where
    semTreeS (Inl f) = semTreeS f
    semTreeS (Inr f) = semTreeS f
    semTreeI (Inl f) = semTreeI f
    semTreeI (Inr f) = semTreeI f

instance (FunType S.:<: t) => SemTreeAG Binding t
  where
    semTreeS (Var v) = SemTree $ do
        EF t <- lookEnv v
        return $ EF $ Sym (SemVar (TypeRep t) v) :&: TypeRep t
    semTreeS (Lam v b) = SemTree $ do
        EF (b' :&: tb) <- semOf b
        EF ta          <- lookEnv v
        return $ EF $ (Sym (SemLam (TypeRep ta) v) :$ b') :&: funType (TypeRep ta) tb

instance (FunType S.:<: t, TypeEq t t) => SemTreeAG Let t
  where
    -- let :: a -> (a -> b) -> b
    semTreeS (Let a f) = SemTree $ do
        EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
        EF (f' :&: tf) <- semOfT (Proxy :: Proxy t) f
        [_, E tb]      <- matchConM tf
        Dict           <- typeEq tf (funType ta tb)
        return $ EF $ (Sym (Sem (flip ($))) :$ a' :$ f') :&: tb

    semTreeI (Let a f)
        | [v] <- argsOf f
        = f |-> Env ((v, typeOf a) : getEnv)

instance (FunType S.:<: t, TypeEq t t) => SemTreeAG App t
  where
    -- let :: (a -> b) -> a -> b
    semTreeS (App f a) = SemTree $ do
        EF (f' :&: tf) <- semOfT (Proxy :: Proxy t) f
        EF (a' :&: ta) <- semOfT (Proxy :: Proxy t) a
        [_, E tb]      <- matchConM tf
        Dict           <- typeEq tf (funType ta tb)
        return $ EF $ (Sym (Sem ($)) :$ f' :$ a') :&: tb

    semTreeI (App f a)
        | [v] <- argsOf f
        = f |-> Env ((v, typeOf a) : getEnv)

instance SubUniverse tLit t => SemTreeAG (Lit tLit) t
  where
    semTreeS (Lit (Dyn ta a)) = SemTree $ Just $ EF $ Sym (Sem a) :&: weakenUniverse ta

instance (BoolType S.:<: t, TypeEq t t) => SemTreeAG Cond t
  where
    -- cond :: Bool -> a -> a -> a
    semTreeS (Cond c t f) = SemTree $ do
        EF (c' :&: tc) <- semOfT (Proxy :: Proxy t) c
        EF (t' :&: tt) <- semOfT (Proxy :: Proxy t) t
        EF (f' :&: tf) <- semOfT (Proxy :: Proxy t) f
        Dict <- typeEq tc boolType
        Dict <- typeEq tt tf
        return $ EF $ (Sym (Sem iff) :$ c' :$ t' :$ f') :&: tt
      where
        iff c t f = if c then t else f

