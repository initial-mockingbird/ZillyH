{-|
Module      : Lilly.Parser.New.Parser.Types
Description : Parsers for @Types@ data type (new parser).
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

We follow the "design patterns for parser combinators" paper by Jamie Willis
and Nicolas Wu. The paper is available at: https://www.cs.tufts.edu/comp/150FP/archive/jamie-willis/parsing-patterns.pdf

-}
module Lilly.Parser.New.Parser.Types where

import Lilly.Parser.New.Parser.Utilities 

import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Definitions.Exports
import Lilly.Parser.New.Definitions.Utilities

import Parser.Patterns hiding (type(<))
import Text.Parsec hiding (token, (<|>))
import Data.Text qualified as Text
import Control.Comonad.Cofree

-----------------------------------------
-- Type Parsers
-----------------------------------------

-- | Parses the @Z@ type.
pZT :: Parser TypeP
pZT = wrapInPos (const PTZ) "Z"

-- | Parses the @R@ type.
pRT :: Parser TypeP
pRT = wrapInPos (const PTR) "R"

-- | Parses the @B@ type.
pBT :: Parser TypeP
pBT = wrapInPos (const PTB) "B"

-- | Parses the @String@ type.
pStringT :: Parser TypeP
pStringT = wrapInPos (const PTString) "String"

-- | Parses the @lazy<T>@ type.
pLazyT :: Parser TypeP -> Parser TypeP
pLazyT pType
  = wrapInPos PTLazy
  $  "lazy"
  *> between "<" ">" (fmap to pType)

-- | Parses the dimention of an array type, e.g. @[,]@ has dimention 2.
pDimention :: Parser Dimention
pDimention = between "[" "]" $ (+1) . length <$> many ","

-- | Parses an array type, e.g. @array[]<Z>@.
pArrayT :: Parser TypeP -> Parser TypeP
pArrayT pType
  = wrapInPos id
  $ PTArray
  <$> ("array" *> pDimention)
  <*> between "<" ">" (fmap to pType)

-- | Parses an arbitrary length tuple type, e.g. @(Z,R,B)@. 
pNtupleT :: Parser TypeP -> Parser TypeP
pNtupleT pType
  = wrapInPos (\(a,b,cs) -> PTNtuple (a,b) cs)
  . between "(" ")"
  $ (,,)
  <$> fmap to pType
  <*> (", " *> fmap to pType)
  <*> sepBy (fmap to pType) ","

-- | Parses a polymorphic type variable, e.g. @'a@. They always begin and are saved with an apostrophe (').
pPolyTypeVar :: Parser TypeVariable
pPolyTypeVar = token $ f <$> char '\'' <*> ident
  where
    f :: Char -> String -> TypeVariable
    f = (.) Text.pack . (:)

-- | Parses a higher-kinded polymorphic type, e.g. @'a<Z,R>@ or @foo<'t>@
pPolyT ::  Parser TypeP -> Parser TypeP
pPolyT pType = wrapInPos f
  $ (,) <$> pPolyTypeVar <*> optionMaybe (bracketed $  pType `sepBy1` ",")
  where
    f :: (TypeVariable, Maybe [TypeP]) -> TypesF (Cofree TypesF IRTokenInfo)
    f (tv, mts) = PTPolymorphic tv (maybe [] (fmap to) mts)

-- | Parses a user-defined type, e.g. @foo<Z,R>@ or @foo@.
pUserDefinedT :: Parser TypeP -> Parser TypeP
pUserDefinedT pType = wrapInPos f
  $ (,) <$> ident <*> optionMaybe (bracketed $  pType `sepBy1` ",")
  where
    f :: (String, Maybe [TypeP]) -> TypesF (Cofree TypesF IRTokenInfo)
    f (name, mts) = PTUserDefined (Text.pack name) (maybe [] (fmap to) mts)

-- | Parses a type "atom", that is, a type with the highest precedence. 
pTypeAtom :: Parser TypeP -> Parser TypeP
pTypeAtom pType =  choice
  [ pZT
  , pRT
  , pBT
  , pStringT
  , pLazyT pType
  , pPolyT pType
  -- collisions with user defined types:
  -- > a[]<3>
  -- > a 
  -- have the same prefix 'a'
  , try $ pArrayT pType
  , pUserDefinedT pType
  -- collisions with tuples
  -- > (a)
  -- > (a,b)
  -- have the same prefix '(a'
  , try $ parens pType
  , pNtupleT pType
  ]

-- | Constructs an arrow type, e.g. @Z => R@.
mkArrowT :: TypeP -> TypeP -> TypeP
mkArrowT l@(linfo :<:  _) r@(rinfo :<:  _)
  = newInfo :<: PArrow (to l) (to r)
  where
    newInfo = IRTokenInfo (tokenStart linfo) (tokenEnd rinfo)

-- | Parses a type. 
pTypes :: Parser TypeP
pTypes = precedence $
  sops InfixR  [mkArrowT <$ "=>"] |-<
  Atom (pTypeAtom pTypes)

