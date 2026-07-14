{-# LANGUAGE FunctionalDependencies #-}
module Lilly.Parser.New.Definitions.Utilities where

import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Definitions.Definitions
import Control.Comonad.Cofree
import Text.Parsec
import Parser.Patterns (keyword)
-----------------------------------
-- Utilities For Boiler Plating 
-----------------------------------

-- Functional Dependency Narrows the
-- Isomorphisms we can express 
-- (can maybe be solved via newtype?), but 
-- helps type inference a LOT
-- Making the core less verbose. 
class Iso a b | a -> b where
  to   :: a -> b
  from :: b -> a


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

instance Iso ProductTypesP (Cofree (ProductTypesF TypeP) IRTokenInfo) where
   to   = unProductTypesP
   from = ProductTypesP
  

instance Iso ActionP (Cofree (ActionF TypeP  ExpressionP ProductTypesP) IRTokenInfo) where
   to   = unActionP
   from = ActionP
  



{- | 
  A pattern for things that are isomorphic to a cofree comonad. Since all of our ASTs are
  newtypes over the cofree comonad, this makes a lot of code less verbose (due to less unwrapping).
-}
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

{- | 
  Mostly used for wrapping an "atom" (highest precedence) parser in a position. Not sure if it has  
  more uses (couldn't figure out how to make it work for infix/prefix/postfix parsers).
-}
wrapInPos :: Iso b (Cofree f IRTokenInfo) => (t -> f (Cofree f IRTokenInfo)) -> Parser t -> Parser b
wrapInPos f = fmap (wrapInPos'' f) . wrapPos

wrapPos :: Parser a -> Parser (IRTokenInfo, a)
wrapPos p = f <$> getPosition <*> p <*> getPosition
  where
    f :: SourcePos -> a -> SourcePos -> (IRTokenInfo, a)
    f st a en = (IRTokenInfo st en, a)

anyKeyword :: Parser ()
anyKeyword = choice $ fmap keyword keywords

