import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable

import Language.Embedded
import Language.Embedded.Sharing

import NanoFeldspar hiding (length)



type Size = Int

getAnn :: (f :&: a) b -> a
getAnn (_ :&: a) = a

dropAnn :: (f :&: a) b -> f b
dropAnn (f :&: _) = f

sizeOf :: Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> Size
sizeOf env = getAnn . expose env

stripAnn :: Functor f => DAG (f :&: a) -> DAG f
stripAnn = appSigFunDAG dropAnn

-- | Alpha equivalence for decorated 'DAG's
alpha :: (EqF f, Binding :<<: f, Functor f, Foldable f) =>
    Defs (f :&: a) -> DAG (f :&: a) -> DAG (f :&: a) -> Bool
alpha env a b = alphaEqDAG env' (stripAnn a) (stripAnn b)
  where
    env' = [(v, stripAnn t) | (v,t) <- env]

-- | Expose the top-most constructor. Like 'expose', specialized for Feldspar and with projection.
open :: (f :<<: FeldF) =>
    Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> Maybe (f (DAG (FeldF :&: Size)))
open env = fmap dropAnn . openS env

-- | Expose the top-most constructor. Like 'expose', specialized for Feldspar and with projection.
openS :: (f :<<: FeldF) =>
    Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> Maybe ((f :&: Size) (DAG (FeldF :&: Size)))
openS env t = case expose env t of
    f :&: s -> fmap (:&: s) $ prj f

-- | Construct a node
close :: (f :<: FeldF) => f (DAG (FeldF :&: Size)) -> DAG (FeldF :&: Size)
close = Term . Inr . sizeProp . inj

sizeProp :: FeldF (DAG (FeldF :&: Size)) -> (FeldF :&: Size) (DAG (FeldF :&: Size))
sizeProp f = f :&: 100  -- TODO

viewLit :: Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> Maybe Int
viewLit env t = do
    Lit (Dyn typ i :: Dynamic FeldTypesSimple) <- open env t
    Dict <- typeEq typ intType
    return i

simplify :: Defs (FeldF :&: Size) -> DAG FeldF -> DAG (FeldF :&: Size)
simplify env t = case f of
    Inr g       -> addDefs ds' $ simplifyUp env' $ close $ fmap (simplify env') g
    Inl (Ref r) -> addDefs ds' $ simplifyUp env' $ Term $ Inl $ Ref r
  where
    (ds, Term f) = splitDefs t
    env'         = transDefs simplify env ds
    ds'          = take (length ds) env'



simplifyUp :: Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> DAG (FeldF :&: Size)

-- a+a  ==>  a*2  (bad rule, but just for illustration)
simplifyUp env t
    | Just (Add a' b') <- open env t
    = case () of
        _ | Just 0 <- viewLit env a' -> b'
          | Just 0 <- viewLit env b' -> a'
          | alpha env a' b'          -> close $ Mul a' (desugarSimp (value 2 :: Data Int))  -- TODO Type
          | otherwise                -> t

-- 0*b  ==>  b
-- a*0  ==>  a
simplifyUp env t
    | Just (Mul a' b') <- open env t
    = case () of
        _ | Just 0 <- viewLit env a' -> a'
          | Just 0 <- viewLit env b' -> b'
          | otherwise                -> t

-- arrLen (parallel l _)  ==>  l
simplifyUp env t
    | Just (ArrLen par)   <- open env t
    , Just (Parallel l _) <- open env par
    = l

-- parallel l (\i -> getIx a i)  ==>  setLength l a
simplifyUp env t
    | Just (Parallel l lam) <- open env t
    , Just (Lam v gix)      <- open env lam
    , Just (GetIx a i)      <- open env gix
    , alpha env i (close $ Var v)
    = a  -- TODO SetLen

-- getIx (parallel l (\j -> body)) i  ==>  let j = i in body
simplifyUp env t
    | Just (GetIx par i)    <- open env t
    , Just (Parallel l lam) <- open env par
    , Just (Lam v body)     <- open env lam
    = subst v i body

simplifyUp env t = t



desugarSimp :: (Syntactic a, PF a ~ FeldF) => a -> DAG (FeldF :&: Size)
desugarSimp = simplify [] . letToDef . unTERM . desugar

term1 :: Data Int -> Data Int
term1 a = share (a*10) $ \b -> share 0 $ \c -> b+c

test_term1 = drawTerm $ stripAnn $ desugarSimp term1

term2 :: Data Int -> Data Int
term2 a = share (a*10) $ \b -> share 0 $ \c -> (share (c+c) $ \cc -> cc*2) + b

test_term2 = drawTerm $ stripAnn $ desugarSimp term2

term3 :: Data Int -> Data Int
term3 a = share (a*3) (\aa -> aa+aa) + a

test_term3 = drawTerm $ stripAnn $ desugarSimp term3

