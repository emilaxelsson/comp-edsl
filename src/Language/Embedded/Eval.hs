{-# LANGUAGE UndecidableInstances #-}

-- | Typed compilation
--
-- See "Typing Dynamic Typing" (Baars and Swierstra, ICFP 2002) and
-- "Efficient Evaluation for Untyped and Compositional Representations of Expressions"
-- (<http://www.cse.chalmers.se/~emax/documents/axelsson2014efficient.pdf>)

module Language.Embedded.Eval
    ( -- * Type universes
      module Data.TypeRep
    , module Data.TypeRep.VarArg
      -- * Typed compilation
    , CExp (..)
    , Compile (..)
    , compile
    , evalTop
    , evalSimple
      -- * Generic compile algebras
    , compileAlg_A_B
    , compileAlg_A_B_C
    , compileAlg_a_a
    , compileAlg_a_a_a
    , compileAlg_a_a_B
    ) where



import Control.Applicative
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import qualified Data.Syntactic as S
import Data.TypeRep hiding ((:+:), Project (..), (:<:) (..))
import Data.TypeRep.VarArg

import Control.Monitoring
import Data.EitherUtils
import Language.Embedded.Syntax
import Language.Embedded.Constructs



----------------------------------------------------------------------------------------------------
-- * Typed compilation
----------------------------------------------------------------------------------------------------

-- | Run-time environment (the values of variables in scope)
type RunEnv t = Map Name (Dynamic t)

-- | Compiled expression
--
-- The first argument to `CExp` is a representation of the result type, and the second argument is a
-- monadic function that computes a value given a runtime environment.
data CExp m t
  where
    CExp :: TypeRep t a -> (RunEnv t -> FunM m (ToRes a)) -> CExp m t

-- For non-functions, it would work to make `RunEnv t ->` part of the `m` in `FunM m`, and that
-- would simplify `Compile` instances a bit. But unfortunately that doesn't work for function types.

-- | An expression compiler parameterized on its compile-time environment. Note that as the compiler
-- does not take an expression as argument, it must be specialized for a specific expression.
--
-- The first argument gives the types of all arguments of the expression to compile. For example,
-- if the expression is @\a -> \b -> c@, then the list should contain (at least) two elements which
-- are taken to be the types of @a@ and @b@ (in that order).
--
-- The second argument gives the types of variables in scope.
type Compiler m t = [E (TypeRep t)] -> Map Name (E (TypeRep t)) -> Either String (CExp m t)

-- | Algebra for compiling expressions
class Compile f m t
  where
    compileAlg :: Alg f (Compiler m t)

-- | Typed compilation
compile :: (Compile f m t, Traversable f) =>
    Map Name (E (TypeRep t)) -> Term f -> Either String (CExp m t)
compile cenv t = cata compileAlg t [] cenv

-- | Evaluate an expression using typed compilation
evalTop :: forall f m t a
    .  ( Typeable t a
       , Compile f m t
       , Traversable f
       , Binding :<<: f
       , FunType S.:<: t
       , TypeEq t t
       )
    => Proxy t -> Proxy m -> Proxy a -> Term f -> Either String (FunM m (ToRes a))
evalTop _ _ _ e = fmap ($ Map.empty) $ go e (typeRep :: TypeRep t a) Map.empty
  where
    go :: Term f -> TypeRep t b -> Map Name (E (TypeRep t))
       -> Either String (RunEnv t -> FunM m (ToRes b))
    go (Term f) t cenv  -- This case handles top-level lambdas
        | Just (Lam v b) <- prj f
        , [E ta, E tb]   <- matchCon t
        = do Dict <- typeEq t (funType ta tb)
             b'   <- go b tb (Map.insert v (E ta) cenv)
             return $ \env -> \a -> b' $ Map.insert v (Dyn ta a) env
    go e te cenv = do
        CExp t c <- compile cenv e :: Either String (CExp m t)
        Dict     <- typeEq t te
        return c

-- | Evaluate an expression using typed compilation. Compilation errors become actual errors. The
-- 'Id' monad is used during evaluation.
evalSimple :: forall f t a
    .  ( Typeable t a
       , Compile f Id t
       , Traversable f
       , Binding :<<: f
       , FunType S.:<: t
       , TypeEq t t
       , VarArg t
       )
    => Proxy t -> Term f -> a
evalSimple pt = runMonadic runId (typeRep :: TypeRep t a) . runEither . evalTop pt pm pa
  where
    pa = Proxy :: Proxy a
    pm = Proxy :: Proxy Id

instance (Compile f m t, Compile g m t) => Compile (f :+: g) m t
  where
    compileAlg (Inl f) = compileAlg f
    compileAlg (Inr f) = compileAlg f

instance (FunType S.:<: t, TypeEq t t, VarArg t, MonadFuel m) => Compile Binding m t
  where
    compileAlg (Var v) _ cenv = do
        E t  <- may (scopeErr v) $ Map.lookup v cenv
        Dict <- nonFunction t
        return $ CExp t $ \env -> do
            Dyn t' a <- may (scopeErr v) $ Map.lookup v env
            Dict     <- typeEq t t'
            tick >> return a
      where
        scopeErr v = "variable " ++ showVar v ++ " not in scope"
    compileAlg (Lam v b) (E t : aenv) cenv = do
        CExp tb b' <- b aenv (Map.insert v (E t) cenv)
        return $ CExp (funType t tb) $ \env -> \a -> b' (Map.insert v (Dyn t a) env)

instance (FunType S.:<: t, TypeEq t t, VarArg t, MonadFuel m) => Compile Let m t
  where
    -- let :: a -> (a -> b) -> b
    compileAlg (Let a f) _ cenv = do
        CExp ta a' <- a [] cenv
        CExp tf f' <- f [E ta] cenv
        [_, E tb]  <- matchConM tf
        Dict       <- typeEq tf (funType ta tb)
        Dict       <- nonFunction ta
        Dict       <- nonFunction tb
        return $ CExp tb $ \env -> do
            a'' <- a' env
            tick >> f' env a''

instance (FunType S.:<: t, TypeEq t t, VarArg t, MonadFuel m) => Compile App m t
  where
    -- app :: (a -> b) -> a -> b
    compileAlg (App f a) _ cenv = do
        CExp ta a' <- a [] cenv
        CExp tf f' <- f [E ta] cenv
        [_, E tb]  <- matchConM tf
        Dict       <- typeEq tf (funType ta tb)
        Dict       <- nonFunction ta
        Dict       <- nonFunction tb
        return $ CExp tb $ \env -> do
            a'' <- a' env
            tick >> f' env a''

instance (SubUniverse tLit t, VarArg tLit, MonadFuel m) => Compile (Lit tLit) m t
  where
    compileAlg (Lit (Dyn ta a)) _ _ = do
        Dict <- nonFunction ta
        return $ CExp (weakenUniverse ta) $ \_ -> tick >> return a

instance (BoolType S.:<: t, TypeEq t t, VarArg t, Applicative m, MonadFuel m) => Compile Cond m t
  where
    -- cond :: Bool -> a -> a -> a
    compileAlg (Cond c t f) _ cenv = do
        CExp tc c' <- c [] cenv
        CExp tt t' <- t [] cenv
        CExp tf f' <- f [] cenv
        Dict       <- typeEq tc boolType
        Dict       <- typeEq tt tf
        Dict       <- nonFunction tt
        return $ CExp tt $ \env -> tick >> iff <$> c' env <*> t' env <*> f' env
      where
        iff c t f = if c then t else f



----------------------------------------------------------------------------------------------------
-- * Generic compile algebras
----------------------------------------------------------------------------------------------------

-- | General implementation of 'compileAlg' for construct of type @A -> B@
compileAlg_A_B :: forall t a b m
    .  ( TypeEq t t
       , Typeable t a
       , Typeable t b
       , NonFunction a
       , NonFunction b
       , Applicative m
       , MonadFuel m
       )
    => (a -> b) -> Compiler m t -> Compiler m t
compileAlg_A_B f a _ cenv = do
    CExp ta a' <- a [] cenv
    Dict       <- typeEq ta (typeRep :: TypeRep t a)
    return $ CExp (typeRep :: TypeRep t b) $ \env -> tick >> f <$> a' env

-- | General implementation of 'compileAlg' for construct of type @A -> B -> C@
compileAlg_A_B_C :: forall t a b c m
    .  ( TypeEq t t
       , Typeable t a
       , Typeable t b
       , Typeable t c
       , NonFunction a
       , NonFunction b
       , NonFunction c
       , Applicative m
       , MonadFuel m
       )
    => (a -> b -> c) -> Compiler m t -> Compiler m t -> Compiler m t
compileAlg_A_B_C f a b _ cenv = do
    CExp ta a' <- a [] cenv
    CExp tb b' <- b [] cenv
    Dict       <- typeEq ta (typeRep :: TypeRep t a)
    Dict       <- typeEq tb (typeRep :: TypeRep t b)
    return $ CExp (typeRep :: TypeRep t c) $ \env -> tick >> f <$> a' env <*> b' env

-- | General implementation of 'compileAlg' for construct of type @p a => a -> a@
compileAlg_a_a :: (PWitness p t t, VarArg t, Functor m, MonadFuel m) =>
    Proxy p -> (forall a . p a => a -> a) -> Compiler m t -> Compiler m t
compileAlg_a_a p f a _ cenv = do
    CExp ta a' <- a [] cenv
    Dict       <- pwit p ta
    Dict       <- nonFunction ta
    return $ CExp ta $ \env -> tick >> f <$> a' env

-- | General implementation of 'compileAlg' for construct of type @p a => a -> a -> a@
compileAlg_a_a_a :: (TypeEq t t, PWitness p t t, VarArg t, Applicative m, MonadFuel m) =>
    Proxy p -> (forall a . p a => a -> a -> a) -> Compiler m t -> Compiler m t -> Compiler m t
compileAlg_a_a_a p f a b _ cenv = do
    CExp ta a' <- a [] cenv
    CExp tb b' <- b [] cenv
    Dict       <- typeEq ta tb
    Dict       <- pwit p ta
    Dict       <- nonFunction ta
    return $ CExp ta $ \env -> tick >> f <$> a' env <*> b' env

-- | General implementation of 'compileAlg' for construct of type @p a => a -> a -> B@
compileAlg_a_a_B :: forall t p b m
    .  ( TypeEq t t
       , PWitness p t t
       , Typeable t b
       , VarArg t
       , Applicative m
       , MonadFuel m
       )
    => Proxy p -> (forall a . p a => a -> a -> b) -> Compiler m t -> Compiler m t -> Compiler m t
compileAlg_a_a_B p f a1 a2 _ cenv = do
    CExp ta1 a1' <- a1 [] cenv
    CExp ta2 a2' <- a2 [] cenv
    Dict         <- pwit p ta1
    Dict         <- typeEq ta1 ta2
    let tb       =  typeRep :: TypeRep t b
    Dict         <- nonFunction ta1
    Dict         <- nonFunction tb
    return $ CExp tb $ \env -> tick >> f <$> a1' env <*> a2' env

