-- | Utilities for working with 'Either'

module Data.EitherUtils where



-- Alternatives:
--
-- http://hackage.haskell.org/package/errors
-- http://hackage.haskell.org/package/MissingH



-- | Extract the 'Right' value, or fail with the 'Left' value as error message
runEither :: Either String a -> a
runEither (Right a)  = a
runEither (Left msg) = error msg

