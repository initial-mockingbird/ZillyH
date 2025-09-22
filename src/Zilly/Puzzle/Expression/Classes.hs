{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}

module Zilly.Puzzle.Expression.Classes
  ( HasArgType(..)
  , HasRetType(..)
  ) where


import Data.Kind (Type)
import Zilly.Puzzle.Types.Exports


class HasArgType ctx tag where
  type ArgType ctx tag :: Type
  argType :: ArgType ctx tag -> Types

class HasRetType ctx tag where
  type RetType ctx tag :: Type
  retType :: RetType ctx tag -> Maybe Types
