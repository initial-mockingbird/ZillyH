{-|
Module      : Lilly.Parser.New.Parser.Action
Description : Parsers for @Action@ data type (new parser).
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

We follow the "design patterns for parser combinators" paper by Jamie Willis
and Nicolas Wu. The paper is available at: https://www.cs.tufts.edu/comp/150FP/archive/jamie-willis/parsing-patterns.pdf

-}
module Lilly.Parser.New.Parser.Action where


import Lilly.Parser.New.Parser.Utilities
import Lilly.Parser.New.Parser.Types
import Lilly.Parser.New.Parser.Expression
import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Definitions.Exports
import Lilly.Parser.New.Definitions.Utilities

import Parser.Patterns hiding (type(<))
import Parser.Numbers

import Text.Parsec hiding (token, (<|>))
import Lilly.Parser.New.Patterns

import Data.String (IsString(..))
import Control.Applicative hiding (optional,many, some)
import Data.Text qualified as Text
import Data.List.NonEmpty qualified as NE
import Data.List (sortOn)
import Data.List qualified as List
import Lilly.Parser.New.Utilities qualified as NPU
import Data.Functor


-- | Parses a @sys.command@ action, e.g. @sys.reset()@ or @sys.foo@. 
pSysCommand :: Parser ActionP
pSysCommand = wrapInPos (`PASysCommand`  [])
    $ ("." $> "reset") <|> ("sys." *> fmap Text.pack ident <* "()" <* optional ";")

-- | Parses a change of VMs, e.g. @::zilly@, @::lilly@ or @::zilly+@.
pModeChange :: Parser ActionP
pModeChange = wrapInPos PModeChange . fmap Text.pack $ choice
    [ "zilly"
    , "lilly"
    , "zilly+"
    ]

-- | Parses a definition action, e.g. @Z x := 42;@.
pDef :: Parser ExpressionP -> Parser ActionP
pDef pExpr = wrapInPos (\(t, name, e) -> PADef t name e)
    $ (,,)
    <$> pTypes
    <*> (Text.pack <$> ident)
    <*> (":=" *> pExpr <* ";")

-- | Parses a reassignment action, e.g. @x := 42;@.
pReassign :: Parser ExpressionP -> Parser ActionP
pReassign pExpr = wrapInPos (uncurry PAReassign)
    $ ((,) . Text.pack <$> ident)
    <*> (":=" *> pExpr <* ";")

-- | Parses an action.
pAction :: Parser ExpressionP -> Parser ActionP
pAction pExpr = choice
    [ pSysCommand
    , pModeChange
    -- lots of collisions
    -- definitions, reassignments and expressions all have "common"
    -- prefixes, thus we go: reassigns -> defs  -> expressions 
    -- the reasoning behind this is that a parsing error in
    -- a reassign will fire faster/first than a parsing error
    -- in a definition (because reassignments are of the form @ident := ...@
    -- , while definitions are of the form @type ident := ...@)
    -- expressions are last cause they can be way way longer.
    , try $ pReassign pExpr
    , try $ pDef pExpr
    , wrapInPos PAExpression pExpr    
    ]




