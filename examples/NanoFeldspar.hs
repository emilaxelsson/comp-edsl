{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
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

import Data.Syntactic (AST (..), (:&:) (..), E (..), EF (..))
import qualified Data.Syntactic as S
import Data.Syntactic.TypeUniverse
import Data.Syntactic.Evaluation (Sem (..))
  -- TODO Make a shim module for these imports. Export from Eval?

import Language.Embedded.Syntax
import Language.Embedded.AG
import Language.Embedded.Constructs
import Language.Embedded.Eval



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

instance Render NUM

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

instance Render ORD

-- | Array manipulation
data Array a
    = GetIx a a
    | ArrLen a
    | Parallel a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''Array]

instance Render Array

-- | For loop
data ForLoop a = ForLoop a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''ForLoop]

instance Render ForLoop

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



----------------------------------------------------------------------------------------------------
-- * Evaluation
----------------------------------------------------------------------------------------------------

-- | 'semOf' specialized to Feldspar
semOfFeld = semOfT (Proxy :: Proxy FeldTypes)

instance SemTreeAG NUM FeldTypes
  where
    semTreeS (Abs a)   = semTreeS_a_a pNum abs a
    semTreeS (Sign a)  = semTreeS_a_a pNum signum a
    semTreeS (Add a b) = semTreeS_a_a_a pNum (+) a b
    semTreeS (Sub a b) = semTreeS_a_a_a pNum (-) a b
    semTreeS (Mul a b) = semTreeS_a_a_a pNum (*) a b

instance SemTreeAG ORD FeldTypes
  where
    semTreeS (LTH a b) = semTreeS_a_a_B pOrd (Prelude.<) a b
    semTreeS (GTH a b) = semTreeS_a_a_B pOrd (Prelude.>) a b
    semTreeS (LTE a b) = semTreeS_a_a_B pOrd (Prelude.<=) a b
    semTreeS (GTE a b) = semTreeS_a_a_B pOrd (Prelude.>=) a b
    semTreeS (Min a b) = semTreeS_a_a_a pOrd Prelude.min a b
    semTreeS (Max a b) = semTreeS_a_a_a pOrd Prelude.max a b

instance SemTreeAG Array FeldTypes
  where
    -- getIx :: [a] -> Index -> a
    semTreeS (GetIx a i) = SemTree $ do
        EF (a' :&: ta) <- semOfFeld a
        EF (i' :&: ti) <- semOfFeld i
        [E telem]      <- matchConM ta
        Dict           <- typeEq ta (listType telem)
        Dict           <- typeEq ti intType
        return $ EF $ (Sym (Sem (!!)) :$ a' :$ i') :&: telem
    -- arrLen :: [a] -> Length
    semTreeS (ArrLen a) = SemTree $ do
        EF (a' :&: ta) <- semOfFeld a
        [E telem]      <- matchConM ta
        Dict           <- typeEq ta (listType telem)
        return $ EF $ (Sym (Sem Prelude.length) :$ a') :&: intType
    -- parallel :: Length -> (Index -> a) -> [a]
    --
    -- parallel :: ( tf ~ (Index -> ta)
    --             , tl ~ Length
    --             )
    --          => tl -> tf -> [ta]
    semTreeS (Parallel l f) = SemTree $ do
        EF (l' :&: tl) <- semOfFeld l
        EF (f' :&: tf) <- semOfFeld f
        [_, E ta]      <- matchConM tf
        Dict           <- typeEq tf (funType intType ta)
        Dict           <- typeEq tl intType
        return $ EF $ (Sym (Sem parallelSem) :$ l' :$ f') :&: listType ta
      where
        parallelSem l ixf = Prelude.take l $ Prelude.map ixf [0..]

    semTreeI (Parallel l ixf)
        | [i] <- argsOf ixf
        = ixf |-> Env ((i, EF intType) : getEnv)
    semTreeI _ = o

instance SemTreeAG ForLoop FeldTypes
  where
    -- forLoop :: Length -> s -> (Index -> s -> s) -> s
    --
    -- forLoop :: ( tl     ~ Length
    --            , tstep  ~ (Index -> (tinit -> tinit))
    --            )
    --         => tl -> tinit -> tstep -> tinit
    semTreeS (ForLoop l init step) = SemTree $ do
        EF (l'    :&: tl)    <- semOfFeld l
        EF (init' :&: tinit) <- semOfFeld init
        EF (step' :&: tstep) <- semOfFeld step
        Dict <- typeEq tl intType
        Dict <- typeEq tstep (funType intType (funType tinit tinit))
        return $ EF $ (Sym (Sem forSem) :$ l' :$ init' :$ step') :&: tinit
      where
        forSem 0 init _    = init  -- Needed when length is unsigned
        forSem l init step = foldl (flip step) init [0..l-1]

    semTreeI (ForLoop _ init step)
        | [i,s] <- argsOf step
        = step |-> Env ((i, EF intType) : (s, typeOf init) : getEnv)

eval :: (Syntactic a, PF a ~ FeldF, Typeable FeldTypes (Internal a)) => a -> Internal a
eval = evalTop (Proxy :: Proxy FeldTypes) . desugar'



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

