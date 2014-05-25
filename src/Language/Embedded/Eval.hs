{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Attribute grammars for typed compilation
-- (see "Typing Dynamic Typing" (Baars and Swierstra, ICFP 2002))

module Language.Embedded.Eval
    ( -- * Type universes
      module Data.Syntactic.TypeUniverse
      -- * Typed compilation
    , CExp (..)
    , cexpOf
    , cexpOfT
    , typeOf
    , CompileAG (..)
    , compile
    , evalTop
    , compileS_A_A
    , compileS_A_A_A
    , compileS_a_a
    , compileS_a_a_a
    , compileS_a_a_B
    ) where



import Control.Applicative
import Data.Maybe (fromJust)

import Data.Syntactic (EF (..))
import Data.Syntactic.Functional (EvalEnv)
import qualified Data.Syntactic as S
import Data.Syntactic.TypeUniverse

import Language.Embedded.Syntax
import Language.Embedded.AG
import Language.Embedded.Constructs



-- | Compiled expression attribute
data CExp t where
    CExp :: TypeRep t a -> (EvalEnv t -> a) -> CExp t

-- | Get the 'CExp' attribute
cexpOf :: (?below :: a -> q, Maybe (CExp t) :< q) => a -> Maybe (CExp t)
cexpOf = below

-- | Get the 'CExp' attribute; fix the type variable by a 'Proxy'
cexpOfT :: (?below :: a -> q, Maybe (CExp t) :< q) => Proxy t -> a -> Maybe (CExp t)
cexpOfT _ = below

-- | Get the type of a 'CExp' attribute
typeOf :: (?below :: a -> q, Maybe (CExp t) :< q) => a -> EF (TR t)
typeOf a = case cexpOf a of
    Just (CExp (TypeRep t) _) -> EF t

-- | Attribute grammar for compiling expressions
class CompileAG f t
  where
    -- | Synthesize the 'CExp' attribute
    compileS :: (Env (EF (TR t)) :< atts) => Syn f atts (Maybe (CExp t))

    -- | Compute the inherited type environment for typed compilation
    compileI :: (Maybe (CExp t) :< atts, Args :< atts) => Inh f atts (Env (EF (TR t)))
    compileI _ = o

-- | Typed compilation
compile :: forall f t
    .  ( CompileAG f t
       , Traversable f
       , Binding :<: f
       )
    => [(Name, EF (TR t))]
    -> Term f
    -> Maybe (CExp t)
compile env = fst . runAG (compileS |*| argsS) compileI' (Env env)
  where
    compileI' :: Inh' f ((Maybe (CExp t), Args), Env (EF (TR t))) (Env (EF (TR t)))
    compileI' = compileI
      -- Why needed?

-- | Evaluate a term using typed compilation
evalTop :: forall f t a
    .  ( Typeable t a
       , CompileAG f t
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
        | Just (CExp t c) <- compile env' e
        , Just Dict       <- typeEq t te
        = c env
      where
        env' = [(v, EF t) | (v, Dyn (TypeRep t) _) <- env]

-- | General implementation of 'compileS' for construct of type @A -> B@
compileS_A_A :: forall t atts q a b
    .  ( TypeEq t t
       , ?below :: atts -> q
       , Maybe (CExp t) :< q
       , Typeable t a
       , Typeable t b
       )
    => (a -> b) -> atts -> Maybe (CExp t)
compileS_A_A f a = do
    CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
    Dict <- typeEq ta (typeRep :: TypeRep t a)
    return $ CExp typeRep $ f <$> a'

-- | General implementation of 'compileS' for construct of type @A -> B -> C@
compileS_A_A_A :: forall t atts q a b c
    .  ( TypeEq t t
       , ?below :: atts -> q
       , Maybe (CExp t) :< q
       , Typeable t a
       , Typeable t b
       , Typeable t c
       )
    => (a -> b -> c) -> atts -> atts -> Maybe (CExp t)
compileS_A_A_A f a b = do
    CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
    CExp tb b' <- cexpOfT (Proxy :: Proxy t) b
    Dict       <- typeEq ta (typeRep :: TypeRep t a)
    Dict       <- typeEq tb (typeRep :: TypeRep t b)
    return $ CExp typeRep $ f <$> a' <*> b'

-- | General implementation of 'compileS' for construct of type @p a => a -> a@
compileS_a_a :: forall t p a q
    .  ( TypeEq t t
       , PWitness p t t
       , ?below :: a -> q
       , Maybe (CExp t) :< q
       )
    => Proxy p -> (forall a . p a => a -> a) -> a -> Maybe (CExp t)
compileS_a_a p f a = do
    CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
    Dict       <- pwit p ta
    return $ CExp ta $ f <$> a'

-- | General implementation of 'compileS' for construct of type @p a => a -> a -> a@
compileS_a_a_a :: forall t p a q
    .  ( TypeEq t t
       , PWitness p t t
       , ?below :: a -> q
       , Maybe (CExp t) :< q
       )
    => Proxy p -> (forall a . p a => a -> a -> a) -> a -> a -> Maybe (CExp t)
compileS_a_a_a p f a b = do
    CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
    CExp tb b' <- cexpOfT (Proxy :: Proxy t) b
    Dict       <- pwit p ta
    Dict       <- typeEq ta tb
    return $ CExp ta $ f <$> a' <*> b'

-- | General implementation of 'compileS' for construct of type @p a => a -> a -> B@
compileS_a_a_B :: forall t p atts q a b
    .  ( TypeEq t t
       , PWitness p t t
       , ?below :: atts -> q
       , Maybe (CExp t) :< q
       , Typeable t b
       )
    => Proxy p -> (forall a . p a => a -> a -> b) -> atts -> atts -> Maybe (CExp t)
compileS_a_a_B p f a b = do
    CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
    CExp tb b' <- cexpOfT (Proxy :: Proxy t) b
    Dict       <- pwit p ta
    Dict       <- typeEq ta tb
    return $ CExp typeRep $ f <$> a' <*> b'

instance (CompileAG f t, CompileAG g t) => CompileAG (f :+: g) t
  where
    compileS (Inl f) = compileS f
    compileS (Inr f) = compileS f
    compileI (Inl f) = compileI f
    compileI (Inr f) = compileI f

instance (FunType S.:<: t, TypeEq t t) => CompileAG Binding t
  where
    compileS (Var v) = do
        EF t <- lookEnv v
        return $ CExp (TypeRep t) $ \env -> fromJust $ do
            Dyn t' a <- lookup v env
            Dict     <- typeEq (TypeRep t) t'
            return a
    compileS (Lam v b) = do
        CExp tb b' <- cexpOf b
        EF ta      <- lookEnv v
        return $ CExp (funType (TypeRep ta) tb) $ \env -> \a -> b' ((v, Dyn (TypeRep ta) a):env)

instance (FunType S.:<: t, TypeEq t t) => CompileAG Let t
  where
    -- let :: a -> (a -> b) -> b
    compileS (Let a f) = do
        CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
        CExp tf f' <- cexpOfT (Proxy :: Proxy t) f
        [_, E tb]  <- matchConM tf
        Dict       <- typeEq tf (funType ta tb)
        return $ CExp tb $ (flip ($)) <$> a' <*> f'

    compileI (Let a f)
        | [v] <- argsOf f
        = f |-> Env ((v, typeOf a) : getEnv)

instance (FunType S.:<: t, TypeEq t t) => CompileAG App t
  where
    -- let :: (a -> b) -> a -> b
    compileS (App f a) = do
        CExp tf f' <- cexpOfT (Proxy :: Proxy t) f
        CExp ta a' <- cexpOfT (Proxy :: Proxy t) a
        [_, E tb]  <- matchConM tf
        Dict       <- typeEq tf (funType ta tb)
        return $ CExp tb $ ($) <$> f' <*> a'

    compileI (App f a)
        | [v] <- argsOf f
        = f |-> Env ((v, typeOf a) : getEnv)

instance SubUniverse tLit t => CompileAG (Lit tLit) t
  where
    compileS (Lit (Dyn ta a)) = Just $ CExp (weakenUniverse ta) $ \_ -> a

instance (BoolType S.:<: t, TypeEq t t) => CompileAG Cond t
  where
    -- cond :: Bool -> a -> a -> a
    compileS (Cond c t f) = do
        CExp tc c' <- cexpOfT (Proxy :: Proxy t) c
        CExp tt t' <- cexpOfT (Proxy :: Proxy t) t
        CExp tf f' <- cexpOfT (Proxy :: Proxy t) f
        Dict       <- typeEq tc boolType
        Dict       <- typeEq tt tf
        return $ CExp tt $ iff <$> c' <*> t' <*> f'
      where
        iff c t f = if c then t else f

