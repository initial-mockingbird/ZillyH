{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-|
Module      : Lilly.Parser.New.Utilities
Description : Utilities mostly useful for parsing modules.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.New.Utilities where

import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Definitions.Definitions
import Control.Comonad.Cofree
import Text.Parsec
import Parser.Patterns (keyword)
import Data.Fix 


-----------------------------------
-- Utilities For Boiler Plating 
-----------------------------------

data Fixity =  InfixL | InfixR | InfixN | Prefix | Postfix deriving (Eq, Ord)

-- Functional Dependency Narrows the
-- Isomorphisms we can express 
-- (can maybe be solved via newtype?), but 
-- helps type inference a LOT
-- Making the core less verbose. 
class Iso a b | a -> b where
  to   :: a -> b
  from :: b -> a

-- instance Iso a a where
--   to = id 
--   from = id 

-- instance (Iso a a', Iso b b') => Iso (a -> b) (a' -> b') where
--     to f a' = to . f $ from a'
--     from g a = from . g $ to a

instance Iso (Cofree (ExpressionF TypeP PatternP GuardP) IRTokenInfo) ExpressionP where 
  to = from 
  from = to 

instance Iso ExpressionP (Cofree (ExpressionF TypeP PatternP GuardP) IRTokenInfo) where
  to   = unExpressionP
  from = ExpressionP

instance Iso PatternP (Cofree PatternF IRTokenInfo) where
  to   = unPatternP
  from = PatternP

instance Iso GuardP (Cofree (GuardF PatternP ExpressionP) IRTokenInfo) where
  to   = unGuardP
  from = GuardP

instance Iso TypeP (Cofree TypesF IRTokenInfo) where
   to   = unTypeP
   from = TypeP


{-# COMPLETE (:<:) #-}
pattern (:<:) :: forall f a1 a2. Iso a1 (Cofree f a2) => a2 -> f (Cofree f a2) -> a1
pattern  a :<: f <- (to -> (a :< f))
  where  a :<: f =  from (a :< f)

-----------------------------------------
-- Aux Parsers
-----------------------------------------

wrapInPos' :: Iso a1 (Cofree f a2) => (t -> f (Cofree f a2)) -> a2 -> t -> a1
wrapInPos' c tki t = tki :<: c t

wrapInPos'' :: Iso a1 (Cofree f a2) => (t -> f (Cofree f a2)) -> (a2, t) -> a1
wrapInPos'' c = uncurry $ wrapInPos' c

wrapInPos :: Iso b (Cofree f IRTokenInfo) => (t -> f (Cofree f IRTokenInfo)) -> Parser t -> Parser b
wrapInPos f = fmap (wrapInPos'' f) . wrapPos

wrapPos :: Parser a -> Parser (IRTokenInfo, a)
wrapPos p = f <$> getPosition <*> p <*> getPosition
  where
    f :: SourcePos -> a -> SourcePos -> (IRTokenInfo, a)
    f st a en = (IRTokenInfo st en, a)

anyKeyword :: Parser ()
anyKeyword = choice $ fmap keyword keywords

------------------------
-- Instance Boilerplate
------------------------

instance ToTypesBase TypeP where
  toTypesBase (_ :<: t) = toTypesBase t


instance ToExprBase ExpressionP where
  toExprBase (_ :<: e) = toExprBase e

instance ToPatternBase PatternP where
  toPatternBase (_ :<: p) = toPatternBase p

instance ToGuardBase GuardP where
  toGuardBase (_ :<: g) = toGuardBase g
