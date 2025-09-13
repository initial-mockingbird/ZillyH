{-# LANGUAGE LambdaCase               #-}
{-# OPTIONS_GHC -Wno-orphans          #-}

module Zilly.Puzzle.Action.Show
  ( Show
  ) where

import Zilly.Puzzle.Action.Base
import Zilly.Puzzle.Environment.TypedMap
import Utilities.ShowM
import Data.List (intercalate)

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
    (TypeDef name constructors)
      -> showString "type " . showString name . showString " := "
      . showString (intercalate " | " $ fmap (\(c,ts) ->
          c ++ if null ts then "" else  intercalate " " (fmap show ts)
        ) constructors)
      . showString ";"
    ABottom -> showString "⊥"
