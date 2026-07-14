{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : Lilly.Parser.New.Parser.Utilities
Description : General Utilities functions (and orphans) for the new parser.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

We follow the "design patterns for parser combinators" paper by Jamie Willis
and Nicolas Wu. The paper is available at: https://www.cs.tufts.edu/comp/150FP/archive/jamie-willis/parsing-patterns.pdf

-}
module Lilly.Parser.New.Parser.Utilities where


import Lilly.Parser.New.Definitions.Exports
import Parser.Patterns hiding (type(<))
import Text.Parsec hiding (token, (<|>))
import Data.String (IsString(..))
import Control.Monad
import Data.Functor
import Lilly.Parser.New.Definitions.Utilities
-------------------------------
-- Useful Orphans
-------------------------------

instance u ~ String => IsString (Parser u ) where
  fromString str
    | str `elem` keywords = keyword str $> str
    | str `elem` reservedOperators
      = token (string str *> notFollowedBy (choice $ void . string <$> ["+","-","=","<",">","%","^",":"]) ) $> str
    | otherwise           = token (string str)

-- | Parses an identifier. 
ident :: Parser String
ident = mkIdent anyKeyword


