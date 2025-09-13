module Zilly.Puzzle.Types.Types
  ( Name
  , TVar(..)
  , Types(..)
  ) where

import Data.Text (Text)
import Data.String (IsString(..))

type Name  = Text


newtype TVar  = TV Name deriving (Eq,Ord)

instance IsString TVar where
  fromString = TV . fromString

data Types
  = TCon Name [Types]
  | TVar TVar
  | TFamApp Name Types [Types]
  deriving (Eq,Ord)

instance IsString Types where
  fromString = TVar . fromString
