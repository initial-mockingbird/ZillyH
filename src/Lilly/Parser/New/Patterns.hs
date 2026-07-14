{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
{-|
Module      : Lilly.Parser.New.Patterns
Description : Pattern Synonyms for the new parser. Useful for easy construction of decorated IR ASTs.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.New.Patterns where

import Lilly.Parser.New.TH 
import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Definitions.Exports
import Lilly.Parser.New.Definitions.Utilities
import Control.Comonad.Cofree

pattern PPGenericInfixOp :: ExpressionP -> Operator ->  ExpressionP -> ExpressionP
pattern PPGenericInfixOp left op right <- _ :<: PInfix (to -> left) op (to -> right)
    where PPGenericInfixOp left@(linfo :<: _) op right@(rinfo :<: _)
            = let newInfo = IRTokenInfo (tokenStart linfo) (tokenEnd rinfo)
              in  newInfo :<: PInfix (to left) op (to right)

pattern PPGenericPrefixOp :: Operator ->  ExpressionP -> ExpressionP
pattern PPGenericPrefixOp op right <- _ :<: PPrefix op (to -> right)
    where PPGenericPrefixOp op right@(rinfo :<: _)
            = rinfo :<: PPrefix op (to right)

pattern PPGenericPostfixOp :: ExpressionP -> Operator ->   ExpressionP
pattern PPGenericPostfixOp left op  <- _ :<: PPostfix (to -> left) op
    where PPGenericPostfixOp  left@(linfo :<: _) op
            = let newInfo = IRTokenInfo (tokenStart linfo) (tokenEnd linfo)
              in  newInfo :<: PPostfix (to left) op 

$(genInfixPatSyns patternTable)


