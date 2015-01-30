{-# LANGUAGE UndecidableInstances #-}

-- | Typed compilation
-- See "Typing Dynamic Typing" (Baars and Swierstra, ICFP 2002) and
-- "Efficient Evaluation for Untyped and Compositional Representations of Expressions"
-- (<http://www.cse.chalmers.se/~emax/documents/axelsson2014efficient.pdf>)

module Language.Embedded.Eval
    ( -- * Type universes
      module Data.TypeRep
      -- * Typed compilation
    , CExp (..)
    , Compile (..)
    , compile
    , evalTop
    , compileAlg_A_B
    , compileAlg_A_B_C
    , compileAlg_a_a
    , compileAlg_a_a_a
    , compileAlg_a_a_B
    ) where



import Control.Applicative
import Data.Maybe (fromJust)

import qualified Data.Syntactic as S
import Data.TypeRep hiding ((:+:), Project (..), (:<:) (..))

import Language.Embedded.Syntax
import Language.Embedded.Constructs
import Language.Embedded.Environment



-- | Run-time environment (the values of variables in scope)
type RunEnv t = Env (Dynamic t)

-- | Compiled expression
--
-- The first argument to `CExp` is a representation of the result type, and the second argument is a
-- function that computes an @a@ given a runtime environment.
data CExp t where
    CExp :: TypeRep t a -> (RunEnv t -> a) -> CExp t

-- | An expression compiler parameterized on its compile-time environment. Note that as the compiler
-- does not take an expression as argument, it must be specialized for a specific expression.
--
-- The first argument gives the types of all arguments of the expression to compile. For example,
-- if the expression is @\a -> \b -> c@, then the list should contain (at least) two elements which
-- are taken to be the types of @a@ and @b@ (in that order).
--
-- The second argument gives the types of variables in scope.
type Compiler t = [E (TypeRep t)] -> Env (E (TypeRep t)) -> Maybe (CExp t)

-- | Algebra for compiling expressions
class Compile f t
  where
    compileAlg :: Alg f (Compiler t)

-- | Typed compilation
compile :: forall f t . (Compile f t, Traversable f) =>
    Env (E (TypeRep t)) -> Term f -> Maybe (CExp t)
compile cenv t = cata compileAlg t [] cenv

-- | Evaluate a term using typed compilation
evalTop :: forall f t a
    .  ( Typeable t a
       , Compile f t
       , Traversable f
       , Binding :<<: f
       , FunType S.:<: t
       , TypeEq t t
       )
    => Proxy t -> Term f -> a
evalTop _ e = go e typeRep emptyEnv
  where
    go :: Term f -> TypeRep t b -> RunEnv t -> b
    go (Term f) t env  -- This case handles top-level lambdas
        | Just (Lam v b) <- prj f
        , [E ta, E tb]   <- matchCon t
        , Just Dict      <- typeEq t (funType ta tb)
        = \a -> go b tb ((v, Dyn ta a) |> env)
    go e te env
        | Just (CExp t c) <- compile env' e
        , Just Dict       <- typeEq t te
        = c env
      where
        env' = fmap (\(Dyn t _) -> E t) env

-- | General implementation of 'compileAlg' for construct of type @A -> B@
compileAlg_A_B :: forall t a b . (TypeEq t t, Typeable t a, Typeable t b) =>
    (a -> b) -> Compiler t -> Compiler t
compileAlg_A_B f a _ cenv = do
    CExp ta a' <- a [] cenv
    Dict       <- typeEq ta (typeRep :: TypeRep t a)
    return $ CExp typeRep $ f <$> a'

-- | General implementation of 'compileAlg' for construct of type @A -> B -> C@
compileAlg_A_B_C :: forall t a b c
    .  ( TypeEq t t
       , Typeable t a
       , Typeable t b
       , Typeable t c
       )
    => (a -> b -> c) -> Compiler t -> Compiler t -> Compiler t
compileAlg_A_B_C f a b _ cenv = do
    CExp ta a' <- a [] cenv
    CExp tb b' <- b [] cenv
    Dict       <- typeEq ta (typeRep :: TypeRep t a)
    Dict       <- typeEq tb (typeRep :: TypeRep t b)
    return $ CExp typeRep $ f <$> a' <*> b'

-- | General implementation of 'compileAlg' for construct of type @p a => a -> a@
compileAlg_a_a :: PWitness p t t =>
    Proxy p -> (forall a . p a => a -> a) -> Compiler t -> Compiler t
compileAlg_a_a p f a _ cenv = do
    CExp ta a' <- a [] cenv
    Dict       <- pwit p ta
    return $ CExp ta $ f <$> a'

-- | General implementation of 'compileAlg' for construct of type @p a => a -> a -> a@
compileAlg_a_a_a :: (TypeEq t t, PWitness p t t) =>
    Proxy p -> (forall a . p a => a -> a -> a) -> Compiler t -> Compiler t -> Compiler t
compileAlg_a_a_a p f a b _ cenv = do
    CExp ta a' <- a [] cenv
    CExp tb b' <- b [] cenv
    Dict       <- typeEq ta tb
    Dict       <- pwit p ta
    return $ CExp ta $ f <$> a' <*> b'

-- | General implementation of 'compileAlg' for construct of type @p a => a -> a -> B@
compileAlg_a_a_B :: (TypeEq t t, PWitness p t t, Typeable t b) =>
    Proxy p -> (forall a . p a => a -> a -> b) -> Compiler t -> Compiler t -> Compiler t
compileAlg_a_a_B p f a b _ cenv = do
    CExp ta a' <- a [] cenv
    CExp tb b' <- b [] cenv
    Dict       <- pwit p ta
    Dict       <- typeEq ta tb
    return $ CExp typeRep $ f <$> a' <*> b'

instance (Compile f t, Compile g t) => Compile (f :+: g) t
  where
    compileAlg (Inl f) = compileAlg f
    compileAlg (Inr f) = compileAlg f

instance (FunType S.:<: t, TypeEq t t) => Compile Binding t
  where
    compileAlg (Var v) _ cenv = do
        E t <- lookEnv v cenv
        return $ CExp t $ \env -> fromJust $ do
            Dyn t' a <- lookEnv v env
            Dict     <- typeEq t t'
            return a
    compileAlg (Lam v b) (E t : aenv) cenv = do
        CExp tb b' <- b aenv ((v, E t) |> cenv)
        return $ CExp (funType t tb) $
            \env -> \a -> b' ((v, Dyn t a) |> env)

instance (FunType S.:<: t, TypeEq t t) => Compile Let t
  where
    -- let :: a -> (a -> b) -> b
    compileAlg (Let a f) _ cenv = do
        CExp ta a' <- a [] cenv
        CExp tf f' <- f [E ta] cenv
        [_, E tb]  <- matchConM tf
        Dict       <- typeEq tf (funType ta tb)
        return $ CExp tb $ (flip ($)) <$> a' <*> f'

instance (FunType S.:<: t, TypeEq t t) => Compile App t
  where
    -- let :: a -> (a -> b) -> b
    compileAlg (App f a) _ cenv = do
        CExp ta a' <- a [] cenv
        CExp tf f' <- f [E ta] cenv
        [_, E tb]  <- matchConM tf
        Dict       <- typeEq tf (funType ta tb)
        return $ CExp tb $ ($) <$> f' <*> a'

instance SubUniverse tLit t => Compile (Lit tLit) t
  where
    compileAlg (Lit (Dyn ta a)) _ _ = Just $ CExp (weakenUniverse ta) $ \_ -> a

instance (BoolType S.:<: t, TypeEq t t) => Compile Cond t
  where
    -- cond :: Bool -> a -> a -> a
    compileAlg (Cond c t f) _ cenv = do
        CExp tc c' <- c [] cenv
        CExp tt t' <- t [] cenv
        CExp tf f' <- f [] cenv
        Dict       <- typeEq tc boolType
        Dict       <- typeEq tt tf
        return $ CExp tt $ iff <$> c' <*> t' <*> f'
      where
        iff c t f = if c then t else f

