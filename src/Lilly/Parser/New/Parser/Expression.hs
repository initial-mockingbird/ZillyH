{-|
Module      : Lilly.Parser.New.Parser.Expression
Description : Parsers for @Expression@ data type (new parser).
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

We follow the "design patterns for parser combinators" paper by Jamie Willis
and Nicolas Wu. The paper is available at: https://www.cs.tufts.edu/comp/150FP/archive/jamie-willis/parsing-patterns.pdf

-}
module Lilly.Parser.New.Parser.Expression where

import Lilly.Parser.New.Parser.Utilities
import Lilly.Parser.New.Parser.Types
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

-----------------------------------------
-- Atoms Parsers
-----------------------------------------

-- | Parses an integer literal, e.g. @42@.
pInt :: Parser ExpressionP
pInt = wrapInPos (PInteger @TypeP @PatternP @GuardP) (token int)

-- | Parses a floating point literal, e.g. @3.14@.
pFloat :: Parser ExpressionP
pFloat = wrapInPos (PFloat @TypeP @PatternP @GuardP) (token (floating3 @Double False))

-- | Parses a variable, e.g. @x@. A variable is just an identifier. 
pVariable :: Parser ExpressionP
pVariable = wrapInPos (PVariable @TypeP @PatternP @GuardP)
  $ Text.pack <$> ident

-- | Parses a boolean literal, e.g. @True@ or @False@.
pBoolean :: Parser ExpressionP
pBoolean = wrapInPos (PBoolean @TypeP @PatternP @GuardP)
  $  (True <$ "True")
  <|> (False <$ "False")

{- | 
  Parses a string literal, e.g. @"Hello, World!"@. String literals
  follows the json string literal format. 
-}
pString :: Parser ExpressionP
pString = wrapInPos (PString @TypeP @PatternP @GuardP) (char '"' >>  Text.pack <$> f)
  where
  f = do
    b <- Text.Parsec.many (noneOf ['"','\\'])
    c <- anyChar
    case c of
      '"' -> pure b
      '\\' -> do
        c' <- anyChar
        mappend (b <> ['\\',c']) <$> f
      _ -> error "pString is buggy."

-- | Parses a parenthesized expression, e.g. @(a + b)@.
pParen :: Parser ExpressionP -> Parser ExpressionP
pParen pExpr = wrapInPos (PParen @TypeP @PatternP @GuardP) (to <$> parens pExpr)

-- | Parses an array expression, e.g. @[1,2,3]@.
pArray :: Parser ExpressionP -> Parser ExpressionP
pArray pExpr = wrapInPos (PArray @TypeP @PatternP @GuardP)
  (fmap to <$> bracketed' (pExpr `sepBy` ","))

-- | Parses a deferred expression, e.g. @'expr'@. 
pDefer :: Parser ExpressionP -> Parser ExpressionP
pDefer pExpr = wrapInPos (PDefer @TypeP @PatternP @GuardP) (to <$> quoted pExpr)

-- | Parses a tuple expression, e.g. @(a,b,c)@.
pNtuple :: Parser ExpressionP -> Parser ExpressionP
pNtuple pExpr = wrapInPos f . parens
  $ (,) <$> fmap to pExpr <* "," <*> (fmap to <$> (pExpr `sepBy1` ","))
  where
    f (a,as) = PNTuple @TypeP @PatternP @GuardP (a, head as) (tail as)

-- | Parses an expression "atom", which is an expression with the highest precedence.
pExpressionAtom :: Parser ExpressionP -> Parser ExpressionP
pExpressionAtom pExpr = choice
  [ -- collissions with float
    try pInt
  , pFloat
  , pBoolean
  , pString
  , pVariable
  , pArray pExpr
  , pDefer pExpr
  -- collisions with tuples
  , try $ pParen pExpr
  , pNtuple pExpr
  ]


-----------------------------------------
-- postfix Parsers
-----------------------------------------

-- | Parses an indexing mode: either an index or a slice.
parseIndexing :: Parser ExpressionP -> Parser (Indexing ExpressionP)
parseIndexing pExpr = f <$> pExpr <*> optionMaybe ("," *> pExpr)
  where
    f :: ExpressionP -> Maybe ExpressionP -> Indexing ExpressionP
    f a Nothing = Index a
    f a (Just b) = Slice (a,b)

-- | Parses an index expression, e.g. @a[0]@. CHECK. should be intercalated with pSlice
pIndex :: Parser ExpressionP -> Parser (ExpressionP -> ExpressionP)
pIndex pExpr = f <$> getPosition <*> bracketed' (parseIndexing pExpr `sepBy1` ",") <*> getPosition
  where
    f :: SourcePos ->  [Indexing ExpressionP] -> SourcePos -> (ExpressionP -> ExpressionP)
    f st idxs en body
      = newInfo :<: PIndex (to body) idxs'
      where
        newInfo = IRTokenInfo st en
        idxs' = NE.fromList $ fmap (fmap to) idxs

pCall :: Parser ExpressionP -> Parser (ExpressionP -> ExpressionP)
pCall pExpr = f <$> getPosition <*> parens 
  ( pExpr `sepBy1` ",") <*> getPosition
  where
    f :: SourcePos -> [ExpressionP] -> SourcePos -> (ExpressionP -> ExpressionP)
    f st args en body
      = newInfo :<: PCall (to body) args'
      where
        newInfo = IRTokenInfo st en
        args' = fmap to args

-----------------------------------------
-- prefix Parsers
-----------------------------------------

-- | Parses a lambda expression, e.g. @fn(x:Z,y:R)=>R->x+y@ or @λ(x:Z,y:R)=>R->x+y@.
-- yes, lambda is a prefix operator
pLambda :: Parser LambdaBinder -> Parser (ExpressionP -> ExpressionP)
pLambda pBinder = f <$> getPosition
  <*>
    ( ("fn" <|> "λ")
      *> parens  ( ((,) <$> pBinder <*> pTypes) `sepBy1` ",")
    )
  <*> (optionMaybe ("=>" *> pTypes) <* "->")
  where
    f :: SourcePos -> [(LambdaBinder, TypeP)] -> Maybe TypeP -> (ExpressionP -> ExpressionP)
    f st binders mtype body@(eTkI :<: _ )
      = newInfo :<: PLambda @_ @PatternP @GuardP binders' mtype (to body)
      where
        newInfo = IRTokenInfo st (tokenEnd eTkI)
        binders' = NE.fromList binders


data OperatorInfo = OperatorInfo
  { operatorName :: Operator
  , operatorPrecedence :: Int
  , operatorAssociativity :: NPU.Fixity
  }

type OperatorTable = [OperatorInfo]

expr :: OperatorTable -> Parser ExpressionP
expr opTable = precedence result
  where

  atoms = Atom (pExpressionAtom (expr opTable))
  fixedTable = 
      [  (sops Prefix [pLambda $ Text.pack <$> ident],1)
      ,  (sops Postfix [pIndex (expr opTable), pCall (expr opTable)], 1000)
      ]
  table = sortOn snd $ fixedTable ++ groupedOpsWithPrec
  result = foldr (\(sops',_) acc -> sops' |-< acc) atoms table

  groupCriteria :: OperatorInfo -> OperatorInfo -> Bool
  groupCriteria op1 op2
    =  operatorPrecedence op1 == operatorPrecedence op2
    && operatorAssociativity op1 == operatorAssociativity op2

  sortedOps = sortOn operatorPrecedence opTable
  groupedOps = List.groupBy groupCriteria sortedOps
  groupedOpsWithPrec = fmap ((,) <$> toSopsWithPrec <*> (operatorPrecedence . head)) groupedOps

  infixPAux op = (`PPGenericInfixOp` operatorName op) <$ fromString (Text.unpack . operatorName $ op)
  prefixPAux op = (operatorName op `PPGenericPrefixOp`) <$ fromString (Text.unpack . operatorName $ op)
  postfixPAux op = (`PPGenericPostfixOp` operatorName op) <$ fromString (Text.unpack . operatorName $ op)

  toSopsWithPrec xs@(x:_) = case operatorAssociativity x of
    NPU.InfixL -> sops InfixL $ infixPAux  <$> xs
    NPU.InfixR -> sops InfixR $ infixPAux  <$> xs
    NPU.InfixN -> sops InfixN $ infixPAux  <$> xs
    NPU.Prefix -> sops Prefix $ prefixPAux <$> xs
    NPU.Postfix -> sops Postfix $ postfixPAux <$> xs
  toSopsWithPrec [] = error "impossible case: toSopsWithPrec called with empty list"   
