{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module NanoFeldspar where



import Prelude hiding
    ( (<), (>), (<=), (>=), min, max
    , length, map, sum, zip, zipWith
    )
import qualified Prelude

import Control.Applicative
import Control.Monad (foldM)

import qualified Data.Syntactic as S

import Control.Monitoring
import Data.EitherUtils
import Language.Embedded hiding (showAST, drawAST, writeHtmlAST)
import qualified Language.Embedded as EDSL
import Language.Embedded.SimpleCodeMotion



----------------------------------------------------------------------------------------------------
-- * Types
----------------------------------------------------------------------------------------------------

type Length = Int
type Index  = Int

-- | Representation of simple types
type FeldTypesSimple
    =     BoolType
    S.:+: IntType
    S.:+: FloatType
    S.:+: ListType

-- | Representation of types (simple types + functions)
type FeldTypes
    =     FunType
    S.:+: FeldTypesSimple

-- | The class of Feldspar types
class    Typeable FeldTypes a => Type a
instance Typeable FeldTypes a => Type a

-- | The class of simple Feldspar types
class    (Type a, Typeable FeldTypesSimple a) => SimpleType a
instance (Type a, Typeable FeldTypesSimple a) => SimpleType a



----------------------------------------------------------------------------------------------------
-- * Abstract syntax
----------------------------------------------------------------------------------------------------

-- | Primitive numeric functions
data NUM a
    = Abs a
    | Sign a
    | Add a a
    | Sub a a
    | Mul a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''NUM]

instance Render  NUM
instance HasVars NUM v

-- | Primitive functions on ordered data
data ORD a
    = LTH a a
    | GTH a a
    | LTE a a
    | GTE a a
    | Min a a
    | Max a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''ORD]

instance Render  ORD
instance HasVars ORD v

-- | Array manipulation
data Array a
    = GetIx a a
    | ArrLen a
    | Parallel a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Array]

instance Render  Array
instance HasVars Array v

-- | For loop
data ForLoop a = ForLoop a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''ForLoop]

instance Render  ForLoop
instance HasVars ForLoop v

-- | Functor representation of Feldspar constructs
type FeldF
    =   Binding
    :+: Let
    :+: Lit FeldTypesSimple
    :+: Cond
    :+: NUM
    :+: ORD
    :+: Array
    :+: ForLoop

-- | Typed Feldspar expressions
newtype Data a = Data {unData :: Term FeldF}
  deriving (Eq)

instance Show (Data a)
  where
    show = show . unData

instance Type a => Syntactic (Data a)
  where
    type Internal (Data a) = a
    type PF       (Data a) = FeldF
    sugar   = Data . desugar'
    desugar = sugar' . unData

-- | Specialization of the 'Syntactic' class for Feldspar
class    (Syntactic a, SimpleType (Internal a), PF a ~ FeldF) => Syntax a
instance (Syntactic a, SimpleType (Internal a), PF a ~ FeldF) => Syntax a



--------------------------------------------------------------------------------
-- * "Backends"
--------------------------------------------------------------------------------

-- | Show the syntax tree using unicode art
showAST :: (Syntactic a, PF a ~ FeldF) => a -> String
showAST = showTerm . codeMotion0 (const True) . desugar'

-- | Draw the syntax tree on the terminal using unicode art
drawAST :: (Syntactic a, PF a ~ FeldF) => a -> IO ()
drawAST = putStrLn . showAST

-- | Write the syntax tree to an HTML file with foldable nodes
writeHtmlAST :: (Syntactic a, PF a ~ FeldF) => a -> IO ()
writeHtmlAST = EDSL.writeHtmlAST "tree.html" . desugar



----------------------------------------------------------------------------------------------------
-- * Evaluation
----------------------------------------------------------------------------------------------------

instance (Applicative m, MonadFuel m) => Compile NUM m FeldTypes
  where
    compileAlg (Abs a)   = compileAlg_a_a pNum abs a
    compileAlg (Sign a)  = compileAlg_a_a pNum signum a
    compileAlg (Add a b) = compileAlg_a_a_a pNum (+) a b
    compileAlg (Sub a b) = compileAlg_a_a_a pNum (-) a b
    compileAlg (Mul a b) = compileAlg_a_a_a pNum (*) a b

instance (Applicative m, MonadFuel m) => Compile ORD m FeldTypes
  where
    compileAlg (LTH a b) = compileAlg_a_a_B pOrd (Prelude.<) a b
    compileAlg (GTH a b) = compileAlg_a_a_B pOrd (Prelude.>) a b
    compileAlg (LTE a b) = compileAlg_a_a_B pOrd (Prelude.<=) a b
    compileAlg (GTE a b) = compileAlg_a_a_B pOrd (Prelude.>=) a b
    compileAlg (Min a b) = compileAlg_a_a_a pOrd Prelude.min a b
    compileAlg (Max a b) = compileAlg_a_a_a pOrd Prelude.max a b

instance (Applicative m, MonadFuel m) => Compile Array m FeldTypes
  where
    -- getIx :: [a] -> Index -> a
    compileAlg (GetIx a i) _ cenv = do
        CExp ta a' <- a [] cenv
        CExp ti i' <- i [] cenv
        [E telem]  <- matchConM ta
        Dict       <- typeEq ta (listType telem)
        Dict       <- typeEq ti intType
        Dict       <- nonFunction telem
        return $ CExp telem $ \env -> tick >> (!!) <$> a' env <*> i' env
    -- arrLen :: [a] -> Length
    compileAlg (ArrLen a) _ cenv = do
        CExp ta a' <- a [] cenv
        [E telem]  <- matchConM ta
        Dict       <- typeEq ta (listType telem)
        return $ CExp intType $ \env -> tick >> Prelude.length <$> a' env
    -- parallel :: Length -> (Index -> a) -> [a]
    --
    -- parallel :: ( tf ~ (Index -> ta)
    --             , tl ~ Length
    --             )
    --          => tl -> tf -> [ta]
    compileAlg (Parallel l f) _ cenv = do
        CExp tl l' <- l [] cenv
        CExp tf f' <- f [E intType] cenv
        [_, E ta]  <- matchConM tf
        Dict       <- typeEq tf (funType intType ta)
        Dict       <- typeEq tl intType
        Dict       <- nonFunction ta
        return $ CExp (listType ta) $ \env -> tick >> parallelSem (l' env) (f' env)
      where
        parallelSem ml mf = do
            l <- ml
            case l of
                0 -> return []
                _ -> Prelude.mapM ((tick >>) . mf) [0 .. l-1]

instance MonadFuel m => Compile ForLoop m FeldTypes
  where
    -- forLoop :: Length -> s -> (Index -> s -> s) -> s
    --
    -- forLoop :: ( tl     ~ Length
    --            , tstep  ~ (Index -> (tinit -> tinit))
    --            )
    --         => tl -> tinit -> tstep -> tinit
    compileAlg (ForLoop l init step) _ cenv = do
        CExp tl    l'    <- l [] cenv
        CExp tinit init' <- init [] cenv
        CExp tstep step' <- step [E intType, E tinit] cenv
        Dict             <- typeEq tl intType
        Dict             <- typeEq tstep (funType intType (funType tinit tinit))
        Dict             <- nonFunction tinit
        return $ CExp tinit $ \env -> tick >> forSem (l' env) (init' env) (step' env)
      where
        forSem ml minit mstep = do
            l    <- ml
            init <- minit
            case l of
                0 -> return init  -- Needed when length is unsigned
                _ -> foldM (\s i -> tick >> mstep i s) init [0..l-1]

eval :: (Syntactic a, PF a ~ FeldF, Typeable FeldTypes (Internal a)) => a -> Internal a
eval = evalSimple (Proxy :: Proxy FeldTypes) . desugar'



----------------------------------------------------------------------------------------------------
-- * Front end
----------------------------------------------------------------------------------------------------

-- | Explicit sharing
share :: (Syntax a, Syntax b) => a -> (a -> b) -> b
share a f = sugar $ smartConstr Let (desugar a) (desugar f)

-- | Literal
value :: Syntax a => Internal a -> a
value a = sugar $ smartConstr (Lit (toDyn a :: Dynamic FeldTypesSimple))

false, true :: Data Bool
false = value False
true  = value True

instance (Num a, SimpleType a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = smartSugar Abs
    signum      = smartSugar Sign
    (+)         = smartSugar Add
    (-)         = smartSugar Sub
    (*)         = smartSugar Mul

(<), (>), (<=), (>=) :: (Ord a, SimpleType a) => Data a -> Data a -> Data Bool
(<)  = smartSugar LTH
(>)  = smartSugar GTH
(<=) = smartSugar LTE
(>=) = smartSugar GTE

min :: (Ord a, SimpleType a) => Data a -> Data a -> Data a
min = smartSugar Min

max :: (Ord a, SimpleType a) => Data a -> Data a -> Data a
max = smartSugar Max

getIx :: SimpleType a => Data [a] -> Data Index -> Data a
getIx = smartSugar GetIx

arrLen :: SimpleType a => Data [a] -> Data Length
arrLen = smartSugar ArrLen

parallel :: SimpleType a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel = smartSugar Parallel

forLoop :: Syntax s => Data Length -> s -> (Data Index -> s -> s) -> s
forLoop l init step = sugar $ smartConstr ForLoop (desugar l) (desugar init) (desugar step)



--------------------------------------------------------------------------------
-- * Vector library
--------------------------------------------------------------------------------

data Vector a
  where
    Indexed :: Data Length -> (Data Index -> a) -> Vector a

instance Syntax a => Syntactic (Vector a)
  where
    type PF (Vector a)       = FeldF
    type Internal (Vector a) = [Internal a]
    desugar = desugar . freezeVector . map resugar
    sugar   = map resugar . thawVector . sugar

length :: Vector a -> Data Length
length (Indexed len _) = len

indexed :: Data Length -> (Data Index -> a) -> Vector a
indexed = Indexed

index :: Vector a -> Data Index -> a
index (Indexed _ ixf) = ixf

(!) :: Vector a -> Data Index -> a
Indexed _ ixf ! i = ixf i

infixl 9 !

freezeVector :: SimpleType a => Vector (Data a) -> Data [a]
freezeVector vec = parallel (length vec) (index vec)

thawVector :: SimpleType a => Data [a] -> Vector (Data a)
thawVector arr = Indexed (arrLen arr) (getIx arr)

zip :: Vector a -> Vector b -> Vector (a,b)
zip a b = indexed (length a `min` length b) (\i -> (index a i, index b i))

unzip :: Vector (a,b) -> (Vector a, Vector b)
unzip ab = (indexed len (fst . index ab), indexed len (snd . index ab))
  where
    len = length ab

permute :: (Data Length -> Data Index -> Data Index) -> (Vector a -> Vector a)
permute perm vec = indexed len (index vec . perm len)
  where
    len = length vec

reverse :: Vector a -> Vector a
reverse = permute $ \len i -> len-i-1

(...) :: Data Index -> Data Index -> Vector (Data Index)
l ... h = indexed (h-l+1) (+l)

map :: (a -> b) -> Vector a -> Vector b
map f (Indexed len ixf) = Indexed len (f . ixf)

zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f a b = map (uncurry f) $ zip a b

fold :: Syntax b => (a -> b -> b) -> b -> Vector a -> b
fold f b (Indexed len ixf) = forLoop len b (\i st -> f (ixf i) st)

sum :: (Num a, Syntax a) => Vector a -> a
sum = fold (+) 0

type Matrix a = Vector (Vector (Data a))

-- | Transpose of a matrix. Assumes that the number of rows is > 0.
transpose :: Type a => Matrix a -> Matrix a
transpose a = indexed (length (a!0)) $ \k -> indexed (length a) $ \l -> a ! l ! k



--------------------------------------------------------------------------------
-- * Examples
--------------------------------------------------------------------------------

scProd :: Vector (Data Float) -> Vector (Data Float) -> Data Float
scProd a b = sum (zipWith (*) a b)

forEach = flip map

-- Matrix multiplication
matMul :: Matrix Float -> Matrix Float -> Matrix Float
matMul a b = forEach a $ \a' ->
               forEach (transpose b) $ \b' ->
                 scProd a' b'



----------------------------------------------------------------------------------------------------
-- * Testing
----------------------------------------------------------------------------------------------------

ex1 :: Data Int
ex1 = share (1+1) (+2)

test1 = eval ex1

ex2 = parallel (10+2) $ \i -> parallel i (*i)

test2 = eval ex2

ex3 = forLoop 100 0 (\i s -> forLoop i s (+))

test3 = eval ex3

test4 = eval scProd [1,2,3] [1,2,3]

