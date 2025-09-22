{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}

module Zilly.Puzzle.Action.Base
  ( A (..)
  ) where

import Zilly.Puzzle.Expression.Exports
import Zilly.Puzzle.Types.Exports
import Zilly.Puzzle.Environment.TypedMap
import Data.Kind (Type)

data A (ctx :: Type) where
  Assign   :: Types -> LensM (E ctx) -> E ctx -> A ctx
  Reassign :: LensM (E ctx) -> [[(E ctx, Maybe (E ctx))]] -> E ctx -> A ctx
  Print    :: E ctx -> A ctx
  SysCommand :: String -> A ctx
  ABottom  :: A ctx
