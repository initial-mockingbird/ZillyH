{-|
Module      : Lilly.Parser.New.Definitions.Definitions 
Description : Data types (and constants) definitions used in the new parser.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Parser types hold extra information about the source code, such as the starting and ending
position of the parsed token. Thus, we need to enrich our base functor IR. And the way
we accomplish that is by using the Cofree Comonad as a means to decorate the tree.

-}
module Lilly.Parser.New.Definitions.Definitions where


import Lilly.Parser.IR.Exports 
import Parser.Patterns qualified as PU
import Text.Parsec hiding (token, (<|>))
import Data.String (IsString(..))

import Data.Functor.Identity
import Control.Comonad.Cofree


------------------------
-- Reserved strings
------------------------

-- | Keywords for Lilly
keywords :: [String]
keywords = stdLib ++
  [ "if"
  , "lazy"
  , "Z"
  , "R"
  , "B"
  , "String"
  , "fn"
  , "λ"
  , "array"
  ]

-- | standard library for Lilly
stdLib :: [String]
stdLib =
  [
  ]

-- | Reserved (expression/type) operators
reservedOperators :: [String]
reservedOperators =
  [ ":="
  , "->"
  , "=>"
  , ":-"
  ]

prefixOperators :: IsString a => [a]
prefixOperators = [ "~"
                  , "-"
                  ]


----------------------------
-- Parser definition
----------------------------

-- | Parser State. Mostly for future use. 
data ParserState = PST
  { pstIdent      :: Int  -- ^ Current Identation level. 
  , insideComment :: Bool -- ^ Whether we are inside a comment or not.
  }

-- | Initial Parser State.
initialPST :: ParserState
initialPST = PST {pstIdent=0,insideComment=False}

-- | Parser Type. Makes things less verbose. 
type Parser a = ParsecT String ParserState Identity a

-------------------------------
-- Useful Parsing Type.
-------------------------------

-- | Token information. This data type will decorate the IR tree.  
data IRTokenInfo = IRTokenInfo
  { tokenStart :: SourcePos -- ^ Starting position of the token.
  , tokenEnd   :: SourcePos -- ^ Ending position of the token.
  }

-------------------------------
-- Parser Types
-------------------------------

-- | IR Type decorated with token information. This is the type that will be used in the parser.
newtype TypeP = TypeP {unTypeP :: Cofree TypesF IRTokenInfo}

instance TypeP PU.< TypeP where
  upcast = id
  downcast = Just

-- | IR Expression decorated with token information. This is the type that will be used in the parser.
newtype ExpressionP = ExpressionP {unExpressionP :: Cofree (ExpressionF TypeP PatternP GuardP) IRTokenInfo}

instance ExpressionP PU.< ExpressionP where
    upcast = id
    downcast = Just

-- | IR Pattern decorated with token information. This is the type that will be used in the parser.
newtype PatternP = PatternP {unPatternP :: Cofree PatternF IRTokenInfo}

instance PatternP PU.< PatternP where
    upcast = id
    downcast = Just

-- | IR Guard decorated with token information. This is the type that will be used in the parser.
newtype GuardP = GuardP {unGuardP :: Cofree (GuardF PatternP ExpressionP) IRTokenInfo}

instance GuardP PU.< GuardP where
    upcast = id
    downcast = Just

-- | IR Product Types decorated with token information. This is the type that will be used in the parser.
newtype ProductTypesP = ProductTypesP {unProductTypesP :: Cofree (ProductTypesF TypeP) IRTokenInfo}

instance ProductTypesP PU.< ProductTypesP where
    upcast = id
    downcast = Just

-- | IR Action decorated with token information. This is the type that will be used in the parser.  
newtype ActionP = ActionP {unActionP :: Cofree (ActionF TypeP ExpressionP ProductTypesP) IRTokenInfo}

instance ActionP PU.< ActionP where
    upcast = id
    downcast = Just