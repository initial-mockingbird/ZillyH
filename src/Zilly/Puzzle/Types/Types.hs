{-# LANGUAGE LambdaCase #-}
module Zilly.Puzzle.Types.Types
  ( Name
  , TVar(..)
  , Types(..)
  , mkRigid
  , mkFlexible
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

mkRigid :: Types -> Types
mkRigid = \case
  TCon n ts -> TCon n $ mkRigid <$> ts
  TVar v -> RTVar v
  TFamApp n t ts -> TFamApp n (mkRigid t) (mkRigid <$> ts)
  TConstraint n t ts y -> TConstraint n (mkRigid t) (mkRigid <$> ts) (mkRigid y)
  RTVar v -> RTVar v


mkFlexible :: Types -> Types
mkFlexible = \case
  TCon n ts -> TCon n $ mkFlexible <$> ts
  RTVar v -> TVar v
  TFamApp n t ts -> TFamApp n (mkFlexible t) (mkFlexible <$> ts)
  TConstraint n t ts y -> TConstraint n (mkFlexible t) (mkFlexible <$> ts) (mkFlexible y)
  TVar v -> TVar v

instance IsString Types where
  fromString = RTVar . fromString
