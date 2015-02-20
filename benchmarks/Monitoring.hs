{-# LANGUAGE BangPatterns #-}

import Criterion.Main
import Criterion.Types

import Control.Monitoring



-- Benchmarks for `Control.Monitoring`. Roughly, the results show that
--
--   * `testI` is ~10% slower than `testRef`
--   * `testE` is ~14% slower than `testRef`
--   * `testFE` is ~14% slower than `testRef`
--   * `testF`, `testEF` and `testFE` take almost identical time: ~5x slower than `testRef`
--   * `testL` is ~8x slower than `testRef`
--   * `testLFE` is ~15x slower than `testRef`
--
-- Additional discoveries:
--
--   * Using `Control.Monad.State.Lazy` made no noticeable difference
--   * Using `Control.Monad.Writer.Lazy` made the tests with logging a bit slower (~25%)
--   * Making `(>>=)` lazy for `Id` made no difference
--   * Using `Int` instead of `Integer` for `FuelT` makes those tests ~30% faster



----------------------------------------------------------------------------------------------------
-- * Expressions with monitoring
----------------------------------------------------------------------------------------------------

add :: (MonadErr m, MonadFuel m) => Int -> Int -> m Int
add a b = tick >> return (a+b)

divv :: (MonadErr m, MonadFuel m) => Int -> Int -> m Int
divv a 0 = throw "division by zero"
divv a b = tick >> return (a `div` b)

iter :: (MonadErr m, MonadLogger m, MonadFuel m) => Int -> (a -> m a) -> a -> m a
iter n f a = do
    logg "iter-start"
    tick
    b <- go n a
    logg "iter-end"
    return b
  where
    go !0 !a = return a
    go !n !a = do
        tick
        go (n-1) =<< f a

expr :: (MonadErr m, MonadLogger m, MonadFuel m) => Int -> m Int
expr a = iter a f a
  where
    f x = iter x g x
    g x = do
        y <- x `divv` x
        add x y



----------------------------------------------------------------------------------------------------
-- * Non-monadic reference implementation
----------------------------------------------------------------------------------------------------

iterRef :: Int -> (a -> a) -> a -> a
iterRef n f = go n
  where
    go !0 !a = a
    go !n !a = go (n-1) $ f a

exprRef :: Int -> Int
exprRef a = iterRef a f a
  where
    f x = iterRef x g x
    g x = x + (x `div` x)



----------------------------------------------------------------------------------------------------
-- * Benchmarks
----------------------------------------------------------------------------------------------------

fuel = 100000000

runE   = runId . execErrT
runL   = runId . evalLoggerT
runF   = runId . flip runFuelT fuel
runEF  = runId . flip runFuelT fuel . execErrT
runFE  = runId . execErrT . flip runFuelT fuel
runLFE = runId . execErrT . flip runFuelT fuel . evalLoggerT

testI   = runId  . expr
testE   = runE   . expr
testL   = runL   . expr
testF   = runF   . expr
testEF  = runEF  . expr
testFE  = runFE  . expr
testLFE = runLFE . expr
testRef = exprRef

main :: IO ()
main = defaultMainWith (defaultConfig {csvFile = Just "bench-results/monitoring.csv"})
    [ bgroup "n=15"
        [ bench "testI"   $ nf testI   15
        , bench "testE"   $ nf testE   15
        , bench "testL"   $ nf testL   15
        , bench "testF"   $ nf testF   15
        , bench "testEF"  $ nf testEF  15
        , bench "testFE"  $ nf testFE  15
        , bench "testLFE" $ nf testLFE 15
        , bench "testRef" $ nf testRef 15
        ]
    , bgroup "n=20"
        [ bench "testI"   $ nf testI   20
        , bench "testE"   $ nf testE   20
        , bench "testL"   $ nf testL   20
        , bench "testF"   $ nf testF   20
        , bench "testEF"  $ nf testEF  20
        , bench "testFE"  $ nf testFE  20
        , bench "testLFE" $ nf testLFE 20
        , bench "testRef" $ nf testRef 20
        ]
    ]

