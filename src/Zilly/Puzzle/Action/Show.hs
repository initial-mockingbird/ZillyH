{-# LANGUAGE LambdaCase               #-}
{-# OPTIONS_GHC -Wno-orphans          #-}

module Zilly.Puzzle.Action.Show
  ( Show
  ) where

import Zilly.Puzzle.Action.Base
import Zilly.Puzzle.Environment.TypedMap
import Utilities.ShowM
instance Show (A ctx) where
  showsPrec _ = \case
    (Assign t x e)
      -> shows t
      . showString " "
      . shows (UT $ varNameM x)
      . showString " := "
      . shows e
      . showString ";"
    (Reassign  x [] e)
      -> shows (UT $ varNameM x)
      . showString " := "
      . shows e
      . showString ";"
    (Reassign x eiss e)
      -> shows (UT $ varNameM x)
      . foldl (\acc eis
        -> acc
        . showString " ["
        . foldl (\acc' (l,mu) ->
            acc' . shows l . maybe id (\u -> showString ".." . shows u) mu
          ) (showString "" )
          eis
        . showString " ]"
        ) id eiss
      . showString " := "
      . shows e
      . showString ";"
    (Print e) -> shows e
    (SysCommand s) -> showString "sys." . showString s . showString "();"
    ABottom -> showString "⊥"
