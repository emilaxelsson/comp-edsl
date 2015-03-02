{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generic representation of EDSL syntax. The types 'Term' and 'TERM' represent abstract syntax.
-- The functions 'smartConstr' and 'smartSugar' are used to define smart constructors, which can be
-- thought of as the concrete EDSL syntax.
--
-- This module reexports many things from the @compdata@ package.
--
-- Example use:
--
-- > {-# LANGUAGE DeriveFoldable, DeriveFunctor, TemplateHaskell #-}
-- >
-- > import Data.Foldable
-- > import Language.Embedded.Syntax
-- >
-- > data Arith a = Int Int | Add a a
-- >   deriving (Functor, Foldable)
-- >
-- > -- Enable rendering
-- > derive [makeShowF, makeShowConstr] [''Arith]
-- > instance Render Arith
-- >
-- > type Exp a = TERM Arith a
-- >
-- > -- Smart constructor for integer literals
-- > int :: Int -> Exp Int
-- > int = smartConstr . Int
-- >
-- > -- Smart constructor for addition
-- > (<+>) :: Exp Int -> Exp Int -> Exp Int
-- > (<+>) = smartConstr Add
--
-- Testing in GHCi:
--
-- > *Main> drawAST (int 1 <+> int 2 :: Exp Int)
-- > Add
-- >  ├╴Int 1
-- >  └╴Int 2

module Language.Embedded.Syntax
    ( -- * Term representation
      Cxt (..)
    , Context
    , Term
    , unTerm
    , simpCxt
    , (:+:) (..)
    , (:<:)
    , inj
    , proj
    , inject
    , project
    , Alg
    , AlgM
    , cata
    , cataM
    , (:&:) (..)
    , module Data.Comp.Render
    , module Data.Comp.Derive
        -- Exports Foldable and Traversable
    , module Data.Comp.Generic
    , TERM (..)
    , ConstrType
    , SmartConstr (..)
    , (:<<:) (..)
    , prj
    , prjTerm
    , withSub
    , withSub'
    , withSubTerm
    , withSubTerm'
      -- * Syntactic sugar
    , Syntactic (..)
    , resugar
    , desugar'
    , sugar'
    , SyntacticN (..)
    , smartSugar
      -- * Rendering
    , showAST
    , drawAST
    , writeHtmlAST
    ) where



import Data.Comp
import Data.Comp.Ops      -- For the constructors of (:+:)
import Data.Comp.Show ()  -- For instances
import Data.Comp.Render
import Data.Comp.Derive
import Data.Comp.Generic



----------------------------------------------------------------------------------------------------
-- * Term representation
----------------------------------------------------------------------------------------------------

-- | 'Term' with a phantom type parameter
newtype TERM f a = TERM {unTERM :: Term f}
    deriving (Eq, Ord)

instance Show (Term f) => Show (TERM f a)
  where
    show = show . unTERM

-- | The type of a constructor corresponding to a smart constructor
type family ConstrType a (sup :: * -> *) (sub :: * -> *)

-- | Smart constructors
class (ConstrType smart (SmartSup smart) (SmartSub smart con) ~ con) => SmartConstr smart con
  where
    type SmartSup smart     :: * -> *
    type SmartSub smart con :: * -> *

    -- | Make a smart constructor
    smartConstr :: con -> smart

type instance ConstrType (Term sup) sup sub = sub (Term sup)

instance (sub :<: sup) => SmartConstr (Term sup) (sub (Term sup))
  where
    type SmartSup (Term sup)                  = sup
    type SmartSub (Term sup) (sub (Term sup)) = sub
    smartConstr = Term . inj

type instance ConstrType (Term sup -> a) sup sub = Term sup -> ConstrType a sup sub

instance
    ( SmartConstr smart con
    , (ConstrType (Term sup -> smart) (SmartSup smart) (SmartSub smart con)) ~ (Term sup -> con)
    ) =>
      SmartConstr (Term sup -> smart) (Term sup -> con)
  where
    type SmartSup (Term sup -> smart)                   = SmartSup smart
    type SmartSub (Term sup -> smart) (Term sup -> con) = SmartSub smart con
    smartConstr f = smartConstr . f

type instance ConstrType (TERM sup a) sup sub = sub (Term sup)

instance (sub :<: sup) => SmartConstr (TERM sup a) (sub (Term sup))
  where
    type SmartSup (TERM sup a)                  = sup
    type SmartSub (TERM sup a) (sub (Term sup)) = sub
    smartConstr = TERM . Term . inj

type instance ConstrType (TERM sup a -> smart) sup sub = Term sup -> ConstrType smart sup sub

instance
    ( SmartConstr smart con
    , (ConstrType (TERM sup a -> smart) (SmartSup smart) (SmartSub smart con)) ~ (Term sup -> con)
    ) =>
      SmartConstr (TERM sup a -> smart) (Term sup -> con)
  where
    type SmartSup (TERM sup a -> smart)                   = SmartSup smart
    type SmartSub (TERM sup a -> smart) (Term sup -> con) = SmartSub smart con
    smartConstr f = smartConstr . f . unTERM

-- | Like ':<:' but slightly weaker. In particular, this class has an instance for ':&:', which
-- ':<:' doesn't have.
class sub :<<: sup
  where
    prjInj :: sup a -> Maybe (sub a, sub b -> sup b)

instance f :<<: f
  where
    prjInj f = Just (f, id)

instance sub :<<: (sub :+: sup)
  where
    prjInj (Inl f) = Just (f, Inl)
    prjInj _       = Nothing

instance (sub :<<: sup) => sub :<<: (f :+: sup)
  where
    prjInj (Inr f) = do
        (g,back) <- prjInj f
        return (g, Inr . back)
    prjInj _ = Nothing

-- | In this instance, the injection will put back the annotation in the same way as in the original
-- argument
instance (sub :<<: sup) => sub :<<: (sup :&: ann)
  where
    prjInj (f :&: a) = do
        (g,back) <- prjInj f
        return (g, (:&:a) . back)

prj :: (sub :<<: sup) => sup a -> Maybe (sub a)
prj = fmap fst . prjInj

prjTerm :: (sub :<<: sup) => Term sup -> Maybe (sub (Term sup))
prjTerm = prj . unTerm

-- The following with* functions are not exported, because I'm not sure they're needed.

withSub :: (sub :<<: sup) => sup a -> (sub a -> sub b) -> Maybe (sup b)
withSub f k = case prjInj f of
    Just (f',back) -> Just $ back $ k f'
    Nothing -> Nothing

withSub' :: (sub :<<: sup) => sup a -> (sub a -> sub a) -> sup a
withSub' f k = case prjInj f of
    Just (f',back) -> back $ k f'
    Nothing -> f

withSubTerm :: (sub :<<: sup) => Term sup -> (sub (Term sup) -> sub (Term sup)) -> Maybe (Term sup)
withSubTerm (Term f) = fmap Term . withSub f

withSubTerm' :: (sub :<<: sup) => Term sup -> (sub (Term sup) -> sub (Term sup)) -> Term sup
withSubTerm' (Term f) = Term . withSub' f



----------------------------------------------------------------------------------------------------
-- * Syntactic sugar
----------------------------------------------------------------------------------------------------

-- | \"Syntactic sugar\" -- types that can be converted to and from 'TERM'
--
-- For details, see "Combining Deep and Shallow Embedding for EDSL"
-- (TFP 2013, <http://www.cse.chalmers.se/~emax/documents/svenningsson2013combining.pdf>).
--
-- It is usually assumed that @(`desugar` (`sugar` a))@ has the same meaning as @a@.
class Syntactic a
  where
    type PF a :: * -> *
    type Internal a
    desugar :: a -> TERM (PF a) (Internal a)
    sugar   :: TERM (PF a) (Internal a) -> a

-- | Sugar-based type casting
resugar :: (Syntactic a, Syntactic b, Internal a ~ Internal b, PF a ~ PF b) => a -> b
resugar = sugar . desugar

desugar' :: Syntactic a => a -> Term (PF a)
desugar' = unTERM . desugar

sugar' :: Syntactic a => Term (PF a) -> a
sugar' = sugar . TERM

instance Syntactic (TERM f a)
  where
    type PF       (TERM f a) = f
    type Internal (TERM f a) = a
    desugar = id
    sugar   = id

-- | N-ary syntactic functions
class SyntacticN f internal | f -> internal
  where
    -- | Informally:
    --
    -- > desugarN f a b ... k = desugar $ f (sugar a) (sugar b) ... (sugar k)
    desugarN :: f -> internal

    -- | Informally:
    --
    -- > sugarN f a b ... k = sugar $ f (desugar a) (desugar b) ... (desugar k)
    sugarN   :: internal -> f

instance (Syntactic f, fi ~ TERM (PF f) (Internal f)) => SyntacticN f fi
  where
    desugarN = desugar
    sugarN   = sugar

instance
    ( Syntactic a
    , ia ~ Internal a
    , pf ~ PF a
    , SyntacticN f fi
    ) =>
      SyntacticN (a -> f) (TERM pf ia -> fi)
  where
    desugarN f = desugarN . f . sugar
    sugarN f   = sugarN . f . desugar

-- | Make a \"sugared\" smart constructor
--
-- Informally:
--
-- > smartSugar f a b ... k = sugar $ TERM $ Term $ inj $ f (desugar' a) (desugar' b) ... (desugar' k)
smartSugar :: (SyntacticN sugar smart, SmartConstr smart con) => con -> sugar
smartSugar = sugarN . smartConstr

-- TODO
-- The following doesn't work:
--
--     data A a = A a a
--
--     aaa :: (Syntactic a, PF a ~ A) => a -> a -> a
--     aaa = smartSugar A
--
-- It seems that the `smart` and `con` type variables (in the type of `smartSugar`) are not
-- completely resolved. A fix is to do:
--
--     aaa = sugarN (smartConstr A :: TERM A a -> TERM A a -> TERM A a)
--
-- or
--
--     aaa a b = sugar $ smartConstr A (desugar a) (desugar b)
--
-- It should be possible to fix this by putting stronger constraints on `SmartConstr` and `SugarN`.
-- But this will probably be easier to do with closed type families.



----------------------------------------------------------------------------------------------------
-- * Rendering
----------------------------------------------------------------------------------------------------

-- | Show the syntax tree using unicode art
showAST :: (Syntactic a, Render (PF a)) => a -> String
showAST = showTerm . desugar'

-- | Draw the syntax tree on the terminal using unicode art
drawAST :: (Syntactic a, Render (PF a)) => a -> IO ()
drawAST = drawTerm . desugar'

-- | Write the syntax tree to an HTML file with foldable nodes
writeHtmlAST :: (Syntactic a, Render (PF a)) => FilePath -> a -> IO ()
writeHtmlAST file = writeHtmlTerm file . desugar'

