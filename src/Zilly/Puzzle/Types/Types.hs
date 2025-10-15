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
  -- Flexible type variable. Can be unified with any type. Can also be instantiated
  | TVar TVar
  | TFamApp Name Types [Types]
  -- TConstraint Eq a [] (a :-> a :-> Bool)
  -- Eq a => (a -> a -> Bool)
  | TConstraint Name Types [Types] Types
  -- Rigid type variable. Cannot be unified with any type except itself in their scope.
  -- Cannot be instantiated.
  | RTVar TVar
  deriving (Eq,Ord)

instance IsString Types where
  fromString = RTVar . fromString
