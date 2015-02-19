-- | Utilities for working with 'Either'

module Data.EitherUtils where



-- Alternatives:
--
-- http://hackage.haskell.org/package/errors
-- http://hackage.haskell.org/package/MissingH




-- | Convert from 'Maybe' to 'Either'
may :: e -> Maybe a -> Either e a
may msg (Just a) = Right a
may msg Nothing  = Left msg

-- | Extract the 'Right' value, or fail with the 'Left' value as error message
runEither :: Either String a -> a
runEither (Right a)  = a
runEither (Left msg) = error msg

