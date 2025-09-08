module Zilly.Puzzle.Types.Types
  ( Name
  , TVar(..)
  , Types(..)
  ) where

import Data.Text (Text)

type Name  = Text


newtype TVar  = TV Name deriving (Eq,Ord)

data Types
  = TCon Name [Types]
  | TVar TVar
  deriving (Eq,Ord)
