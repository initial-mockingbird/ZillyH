{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# OPTIONS_GHC -Wno-orphans          #-}

module Zilly.Puzzle.Types.Show
  ( Show
  ) where

import Zilly.Puzzle.Types.Types
import Zilly.Puzzle.Types.Patterns
import Data.Text qualified as Text


instance Show Types where
  showsPrec p = \case
    ARecord (f : fields)
      -> showString "{ "
      . foldr (\(n,t) acc -> showString (Text.unpack n) . showString ": " . shows t . showString ", " . acc) (showString $ (\(n,t) -> Text.unpack n <> ": " <> show t) f)  fields
      . showString "}"
    ARecord [] -> showString "{}"
    TCon a [] -> showString $ Text.unpack a
    NDArray n a
      -> showString "array["
      . showString (replicate (n-1) ',')
      . showString "]<"
      . shows a
      . showString ">"
    TCon "Tuple" [a,b] -> showString "(" . shows a . showString ", " . shows b . showString ")"
    a :-> b -> showParen (p > 0) $ showsPrec 1 a . showString " => " . shows b
    TCon a (x:xs)
      -> showString (Text.unpack a) . showString "<"
      . foldr (\arg acc -> shows arg . showString ", " . acc) (shows x) xs
      . showString ">"
    TVar (TV n) -> showString $ Text.unpack n
    TFamApp n x xs
      -> showString (Text.unpack n) . showString "<"
      . foldr (\arg acc -> shows arg . showString ", " . acc) (shows x) xs
      . showString ">"
