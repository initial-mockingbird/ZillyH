module Zilly.Puzzle.Action.Classes
  ( HasTypeEnv(..)

  ) where

import Zilly.Puzzle.Types.Exports

class HasTypeEnv m where

  declareType :: String -> [(String,[Types])] -> m ()
  updateType  :: String -> [(String,[Types])] -> m ()
  lookupType  :: String -> m (Maybe [(String,[Types])])
  -- Given a constructor name, return the list of types it can belong to
  -- and their arguments.
  lookupCons  :: String -> m (Maybe (Types, [Types]))
