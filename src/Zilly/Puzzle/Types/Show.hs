{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# OPTIONS_GHC -Wno-orphans          #-}
{-# LANGUAGE ExplicitForAll #-}

module Zilly.Puzzle.Types.Show
  ( Show
  ) where

import Zilly.Puzzle.Types.Types
import Zilly.Puzzle.Types.Patterns
import Data.Text qualified as Text
import Data.Set (Set)
import Data.Set qualified as S
import Data.List (intercalate)

instance Show Types where
  showsPrec p = \case
    TConstraints cs t | not (null cs)
      -> showConstraints (S.toList cs)
      . showString " |- "
      . showsPrec p t

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
      . showString  (intercalate ", " (map show (x:xs)))
      . showString ">"

    RTVar (TV n) -> showString $ Text.unpack n
    TVar (TV n) -> showString $ Text.unpack n
    TFamApp n x xs
      -> showString (Text.unpack n) . showString "<"
      . showString (intercalate ", " (map show (x:xs)))
      . showString ">"
    TConstraints cs t | null cs
      -> showsPrec p t

    _ -> error $ "Cannot show type: " ++ show p

    where
      showConstraint :: (Name, Types, [Types]) -> ShowS
      showConstraint (n, t, ts)
        = showString (Text.unpack n) . showString "<"
        . showString (intercalate ", " (map show (t:ts)))
        . showString ">"
      showConstraints []     = id
      showConstraints [c]    = showConstraint c
      showConstraints (c:cs) = showConstraint c . showString ", " . showConstraints cs
