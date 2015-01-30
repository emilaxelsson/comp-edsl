-- | Type for and operations on variable environments

module Language.Embedded.Environment where



import Data.Map as Map

import Data.Syntactic.Functional (Name (..))



-- | Environment with information about variables in scope
type Env a = Map Name a

emptyEnv :: Env a
emptyEnv = empty

singleEnv :: Name -> a -> Env a
singleEnv = Map.singleton

-- | Insert a mapping into an environment
insEnv :: Name -> a -> Env a -> Env a
insEnv = insert

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

