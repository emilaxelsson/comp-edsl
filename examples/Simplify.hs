import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable

import Language.Embedded
import Language.Embedded.Sharing

import NanoFeldspar hiding (length)



type Size = Int

sizeOf :: DAG (FeldF :&: Size) -> Size
sizeOf = getAnn . whereBody . unTerm

-- | Expose the top-most constructor. Like 'expose', specialized for Feldspar and with projection.
open :: (f :<: FeldF) =>
    Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> Maybe (f (DAG (FeldF :&: Size)))
open env = proj . dropAnn . expose env

-- | Construct a node
close :: (f :<: FeldF) => f (DAG (FeldF :&: Size)) -> DAG (FeldF :&: Size)
close f = Term $ Where [] $ sizeProp $ inj f

sizeProp :: FeldF (DAG (FeldF :&: Size)) -> (FeldF :&: Size) (DAG (FeldF :&: Size))
sizeProp f = f :&: 100  -- TODO

viewLit :: Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> Maybe Int
viewLit env t = do
    Lit (Dyn typ i :: Dynamic FeldTypesSimple) <- open env t
    Dict <- typeEq typ intType
    return i

simplify :: Defs (FeldF :&: Size) -> DAG FeldF -> DAG (FeldF :&: Size)
simplify env (Term (Where ds f)) = addDefs ds' $ simplifyUp env' def
  where
    env' = transDefs simplify env ds
    ds'  = take (length ds) env'
    def  = close $ fmap (simplify env') f  -- Default result



simplifyUp :: Defs (FeldF :&: Size) -> DAG (FeldF :&: Size) -> DAG (FeldF :&: Size)

-- a+a  ==>  a*2  (bad rule, but just for illustration)
simplifyUp env t
    | Just (Add a' b') <- open env t
    = case () of
        _ | Just 0 <- viewLit env a' -> b'
          | Just 0 <- viewLit env b' -> a'
          | alphaEqDAG a' b'         -> close $ Mul a' (desugarSimp (value 2 :: Data Int))  -- TODO Type
          | otherwise                -> t

  -- TODO The use of alphaEqDAG assumes that equal terms have the same free variables (could be
  --      variables that are in scope from higher up). If this is not the case, use a different
  --      function that looks up free variables in the environment and maybe uses hashing to improve
  --      performance.

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
    , alphaEqDAG i (close $ Var v)
    = a  -- TODO SetLen

-- getIx (parallel l (\j -> body)) i  ==>  let j = i in body
simplifyUp env t
    | Just (GetIx par i)    <- open env t
    , Just (Parallel l lam) <- open env par
    , Just (Lam v body)     <- open env lam
    = addDefs [(v,i)] body

simplifyUp env t = t



desugarSimp :: (Syntactic a, PF a ~ FeldF) => a -> DAG (FeldF :&: Size)
desugarSimp = simplify [] . termToDAG . unTERM . desugar



term1 :: Data Int -> Data Int
term1 a = share (a*10) $ \b -> share 0 $ \c -> b+c

-- test_term1_1 = prop_DAG $ unTERM $ desugar term1
-- test_term1_2 = prop_foldWithLet (\f -> 1 + Foldable.sum f) $ unTERM $ desugar term1

test_term1 = drawTerm $ dagToTerm $ stripAnnDAG $ desugarSimp term1

term2 :: Data Int -> Data Int
term2 a = share (a*10) $ \b -> share 0 $ \c -> (share (c+c) $ \cc -> cc*2) + b

-- test_term2_1 = prop_DAG $ unTERM $ desugar term2
-- test_term2_2 = prop_foldWithLet (\f -> 1 + Foldable.sum f) $ unTERM $ desugar term2

test_term2 = drawTerm $ dagToTerm $ stripAnnDAG $ desugarSimp term2

term3 :: Data Int -> Data Int
term3 a = share (a*2) (\aa -> aa+aa) + a

-- test_term3_1 = prop_DAG $ unTERM $ desugar term3
-- test_term3_2 = prop_foldWithLet (\f -> 1 + Foldable.sum f) $ unTERM $ desugar term3

test_term3 = drawTerm $ dagToTerm $ stripAnnDAG $ desugarSimp term3

