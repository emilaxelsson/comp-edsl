-- | Type for and operations on variable environments

module Language.Embedded.Environment where



import Data.List as List
import Data.Map as Map

import Data.Syntactic.Functional (Name (..))



----------------------------------------------------------------------------------------------------
-- * No duplicates
----------------------------------------------------------------------------------------------------

-- | Environment with information about variables in scope
type Env a = Map Name a

-- | Empty environment
emptyEnv :: Env a
emptyEnv = empty

-- | Environment with a single mapping
singleEnv :: Name -> a -> Env a
singleEnv = Map.singleton

-- | Insert a mapping into an environment
insEnv :: Name -> a -> Env a -> Env a
insEnv = Map.insert

-- | Insert a mapping into an environment
(|>) :: (Name,a) -> Env a -> Env a
(v,a) |> env = insEnv v a env

-- | Lookup a name in an environment
lookEnv :: Name -> Env a -> Maybe a
lookEnv = Map.lookup

-- | Like 'lookEnv' but failing with the given message in case the name is not found
lookEnvNote :: String -> Name -> Env a -> a
lookEnvNote msg v env = case lookEnv v env of
    Nothing -> error msg
    Just a -> a

-- | List the content of an environment
--
-- The order of the result has nothing to do with the order in which the elements were inserted.
toListEnv :: Env a -> [(Name, a)]
toListEnv = Map.toList

-- | Create an environment from a list
--
-- If the same name appears several times, the last one has precedence.
fromListEnv :: [(Name, a)] -> Env a
fromListEnv = Map.fromList



----------------------------------------------------------------------------------------------------
-- * Duplicates
----------------------------------------------------------------------------------------------------

-- | Environment with potential duplicates
newtype ENV a = ENV {toListENV :: [(Name,a)]}
  deriving (Eq, Ord, Show)

-- | Empty environment
emptyENV :: ENV a
emptyENV = ENV []

-- | Environment with a single mapping
singleENV :: Name -> a -> ENV a
singleENV v a = ENV [(v,a)]

-- | Insert a mapping into an environment. For functions like 'lookENV', the new name shadows any
-- existing occurrences of the same name.
insENV :: Name -> a -> ENV a -> ENV a
insENV v a (ENV env) = ENV ((v,a) : env)

-- | Insert a mapping into an environment. Newly inserted names shadow old names.
(||>) :: (Name,a) -> ENV a -> ENV a
def ||> ENV env = ENV (def:env)

-- | Lookup a name in an environment
lookENV :: Name -> ENV a -> Maybe a
lookENV v = List.lookup v . toListENV

-- | Like 'lookENV' but failing with the given message in case the name is not found
lookENVNote :: String -> Name -> ENV a -> a
lookENVNote msg v env = case lookENV v env of
    Nothing -> error msg
    Just a -> a

-- | Delete all occurrences of a name from a environment
delENV :: Name -> ENV a -> ENV a
delENV v (ENV env) = ENV [def | def <- env, fst def /= v]

-- | Lookup a name in an environment; return its definition and the rest of the environment
splitENV :: Name -> ENV a -> Maybe (a, ENV a)
splitENV v (ENV env) = case dropWhile ((v/=) . fst) env of
    def:env' -> Just (snd def, ENV env')
    _ -> Nothing

