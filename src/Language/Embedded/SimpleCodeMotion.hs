-- | Simple code motion transformation performing common sub-expression elimination and variable
-- hoisting. Note that the implementation is very inefficient.
--
-- The code is based on an implementation by Gergely Dévai.

module Language.Embedded.SimpleCodeMotion
    ( codeMotion
    , codeMotion0
    ) where



import Control.Monad.State
import qualified Data.Foldable as Foldable
import Data.Set as Set
import Data.Traversable (traverse)

import Language.Embedded.Syntax
import Language.Embedded.Constructs
import Language.Embedded.Algorithms



-- | Substituting a sub-expression. Assumes no variable capturing in the expressions involved.
substitute :: (EqF f, Binding :<: f, Functor f, Foldable f)
    => Term f  -- ^ Sub-expression to be replaced
    -> Term f  -- ^ Replacing sub-expression
    -> Term f  -- ^ Whole expression
    -> Term f
substitute target new t@(Term f)
    | alphaEq target t = new
    | otherwise        = Term $ fmap (substitute target new) f

-- | Count the number of occurrences of a sub-expression
count :: (EqF f, Binding :<: f, Functor f, Foldable f)
    => Term f  -- ^ Expression to count
    -> Term f  -- ^ Expression to count in
    -> Int
count a b@(Term f)
    | alphaEq a b = 1
    | otherwise   = Foldable.sum $ fmap (count a) f

-- | Environment for the expression in the 'choose' function
data MotionEnv f = MotionEnv
    { inLambda :: Bool  -- ^ Whether the current expression is inside a lambda
    , counter  :: Term f -> Int
        -- ^ Counting the number of occurrences of an expression in the
        -- environment
    , dependencies :: Set Name
        -- ^ The set of variables that are not allowed to occur in the chosen
        -- expression
    }

independent :: (Binding :<: f, Functor f, Foldable f) => MotionEnv f -> Term f -> Bool
independent env t
    | Just (Var v) <- project t
    = not (v `member` dependencies env)
independent env (Term f) = Foldable.and $ fmap (independent env) f

isVariable :: (Binding :<: f) => Term f -> Bool
isVariable t
    | Just (Var _) <- project t = True
    | otherwise = False

-- | Checks whether a sub-expression in a given environment can be lifted out
liftable :: (Binding :<: f, Functor f, Foldable f) => MotionEnv f -> Term f -> Bool
liftable env a = independent env a && not (isVariable a) && heuristic
    -- Lifting dependent expressions is semantically incorrect
    -- Lifting variables would cause `codeMotion` to loop
  where
    heuristic = inLambda env || (counter env a > 1)

-- | Choose a sub-expression to share
choose :: forall f . (EqF f, Binding :<: f, Functor f, Foldable f) =>
    (Term f -> Bool) -> Term f -> Maybe (Term f)
choose hoistOver a = chooseEnvSub initEnv a
  where
    initEnv = MotionEnv
        { inLambda     = False
        , counter      = flip count a
        , dependencies = empty
        }

    chooseEnv :: MotionEnv f -> Term f -> Maybe (Term f)
    chooseEnv env b
        | liftable env b
        = Just b
    chooseEnv env b
        | hoistOver b = chooseEnvSub env b
        | otherwise   = Nothing

    -- | Like 'chooseEnv', but does not consider the top expression for sharing
    chooseEnvSub :: MotionEnv f -> Term f -> Maybe (Term f)
    chooseEnvSub env t
        | Just (Lam v b) <- project t
        = chooseEnv (env' v) b
      where
        env' v = env
            { inLambda     = True
            , dependencies = insert v (dependencies env)
            }
    chooseEnvSub env (Term f) = Foldable.foldr mplus Nothing $ fmap (chooseEnv env) f

-- | Perform common sub-expression elimination and variable hoisting
codeMotion :: forall f . (EqF f, Binding :<: f, Let :<: f, Traversable f)
    => (Term f -> Bool)
          -- ^ Control wether a sub-expression can be hoisted over the given expression
    -> Term f
    -> State Name (Term f)
codeMotion hoistOver a@(Term f)
    | Just b <- choose hoistOver a = share b
    | otherwise                    = fmap Term $ traverse (codeMotion hoistOver) f
  where
    share :: Term f -> State Name (Term f)
    share b = do
        b'   <- codeMotion hoistOver b
        v    <- get; put (v+1)
        body <- codeMotion hoistOver $ substitute b (inject (Var v)) a
        return $ inject $ Let b' $ inject $ Lam v body

codeMotion0 :: (EqF f, Binding :<: f, Let :<: f, Traversable f)
    => (Term f -> Bool)
          -- ^ Control wether a sub-expression can be hoisted over the given expression
    -> Term f
    -> Term f
codeMotion0 hoistOver = flip evalState 0 . codeMotion hoistOver

