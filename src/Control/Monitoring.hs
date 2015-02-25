-- | Monads for monitoring and controlling algorithms
--
-- The different monitoring effects are:
--
-- * Exceptions (represented by 'ErrT' and the class @`MonadErr` String@)
-- * Logging    (represented by 'LoggerT' and the class 'MonadLogger')
-- * Fuel       (represented by 'FuelT' and the class 'MonadFuel')
--
-- These effects can be enabled by combining the transformers @`ErrT` String@, 'LoggerT' and
-- 'FuelT'. By using 'Id' at the bottom of the stack, it is possible to leave out any of the
-- transformers and still have an instance for all of the above classes. For the left out
-- transformers, the corresponding monitoring methods are then simply no-ops.

module Control.Monitoring where



import Control.Applicative
import Control.Monad.Error
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict



----------------------------------------------------------------------------------------------------
-- * Identity monad
----------------------------------------------------------------------------------------------------

-- | Identity monad (to avoid making orphan instances for the standard identity monad)
newtype Id a = Id { runId :: a }
  deriving (Eq, Ord, Functor)

instance Show a => Show (Id a)
  where
    show = show . runId

instance Applicative Id
  where
    pure = Id
    Id f <*> Id a = Id (f a)

-- | (>>=) is strict in the bound value, in order to propagate errors
instance Monad Id
  where
    return = Id
    Id a >>= k = k $! a



----------------------------------------------------------------------------------------------------
-- * Exceptions
----------------------------------------------------------------------------------------------------

-- | Exception monad
type ErrT = ErrorT String

-- | Run function for 'ErrT'
runErrT :: Monad m => ErrT m a -> m (Either String a)
runErrT = runErrorT

-- | Run function for 'ErrT' that throws an error in case of an exception
execErrT :: Monad m => ErrT m a -> m a
execErrT m = do
    ea <- runErrT m
    case ea of
        Left msg -> error msg
        Right a  -> return a

type MonadErr = MonadError String

throw :: MonadErr m => String -> m a
throw = throwError

catch :: MonadErr m => m a -> (String -> m a) -> m a
catch = catchError

-- | Fake instance where 'throwError' returns 'error'
instance MonadError String Id
  where
    throwError = error
    catchError a _ = a

may :: MonadErr m => String -> Maybe a -> m a
may msg Nothing  = throw msg
may msg (Just a) = return a



----------------------------------------------------------------------------------------------------
-- * Logging
----------------------------------------------------------------------------------------------------

-- | Logging monad
type LoggerT = WriterT [String]

-- | Run function for 'LoggerT'
runLoggerT :: LoggerT m a -> m (a, [String])
runLoggerT = runWriterT

-- | Run function for 'LoggerT'
evalLoggerT :: Functor m => LoggerT m a -> m a
evalLoggerT = fmap fst . runWriterT

type MonadLogger = MonadWriter [String]

logg :: MonadLogger m => String -> m ()
logg msg = tell [msg]

-- | Fake instance that ignores the logging
instance MonadWriter [String] Id
  where
    tell _ = Id ()
    listen = error "listen not implemented for Id"
    pass   = error "pass not implemented for Id"



----------------------------------------------------------------------------------------------------
-- * Fuel
----------------------------------------------------------------------------------------------------

-- | A computation \"on fuel\"
type FuelT m = StateT Integer m

type MonadFuel m = (MonadErr m, MonadState Integer m)

-- | Run a computation on fuel
runFuelT :: Monad m
    => FuelT m a  -- ^ Computation on fuel
    -> Integer    -- ^ Amount of fuel to start with
    -> m a
runFuelT = evalStateT

-- | Consumes one unit of fuel and throws an error when the fuel goes below 0
tick :: MonadFuel m => m ()
tick = do
    fuel <- get
    let fuel' = fuel-1
    when (fuel' < 0) $ throwError "out of fuel"
    put fuel'

-- | Fake instance that always has the state 1 (so that there's always fuel left)
instance MonadState Integer Id
  where
    get   = return 1
    put _ = return ()

