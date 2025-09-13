{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE LambdaCase            #-}

module Zilly.Puzzle.Expression.Classes
  ( HasArgType(..)
  , HasRetType(..)
  , typeOf
  ) where


import Data.Kind (Type)
import Zilly.Puzzle.Types.Exports hiding (ARecord)
import Zilly.Puzzle.Expression.Base

class HasArgType ctx tag where
  type ArgType ctx tag :: Type
  argType :: ArgType ctx tag -> Types

class HasRetType ctx tag where
  type RetType ctx tag :: Type
  retType :: RetType ctx tag -> Maybe Types

typeOf :: E ctx -> Types
typeOf = \case
  ValZ _         -> Z
  ValF _         -> F
  ValB _         -> ZBool
  ValS _         -> ZString
  Var t _        -> t
  If t _ _ _     -> t
  Lambda t _ _ _ -> t
  Defer t _      -> t
  App t _ _      -> t
  LambdaC t _ _ _ _ -> t
  LazyC t _ _ _    -> t
  MkTuple t _ _ _  -> t
  MkArray t _      -> t
  Bottom t _ _    -> t
  ArraySlice t _ _ -> t
  DotApp t _ _    -> t
  Cons t _ _      -> t
  ARecord t _     -> t
  Match t _ _    -> t
  ConsV t _ _    -> t
  ARecordV t _  -> t
