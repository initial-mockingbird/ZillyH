{-|
Module      : Lilly.Parser.IR.Utilities
Description : Utility functions for the IR. Mostly used for turning things into fixpoint representations for @toString@ purposes.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.IR.Utilities where

import Lilly.Parser.IR.IR        
import Data.Fix ( Fix(Fix) )
import Control.Comonad.Cofree ( Cofree((:<)) )

{-|
    @Types@ on their own should be the minimal data type which a @toString@ function can be implemented.
    Thus, we need a way to convert enriched trees (i.e: tagged via the Cofree Comonad) to our
    fixed point representation. This is what the class does. 
-}
class ToTypesBase a where 
    toTypesBase :: a -> Types

instance ToTypesBase a => ToTypesBase (TypesF a) where 
    toTypesBase PTZ = Fix PTZ
    toTypesBase PTR = Fix PTR
    toTypesBase PTB = Fix PTB
    toTypesBase PTString = Fix PTString
    toTypesBase (PTLazy a) = Fix . PTLazy $ toTypesBase a
    toTypesBase (PTArray d a) = Fix . PTArray d $ toTypesBase a
    toTypesBase (PTNtuple (a1,a2) as) = Fix . PTNtuple (toTypesBase a1, toTypesBase a2) $ toTypesBase <$> as
    toTypesBase (PTPolymorphic name as) = Fix . PTPolymorphic name $ toTypesBase <$> as
    toTypesBase (PTUserDefined name as) = Fix . PTUserDefined name $ toTypesBase <$> as
    toTypesBase (PArrow a1 a2) = Fix . PArrow (toTypesBase a1) $ toTypesBase a2



{-|
    @Expression@ on their own should be the minimal data type which a @toString@ function can be implemented.
    Thus, we need a way to convert enriched trees (i.e: tagged via the Cofree Comonad) to our
    fixed point representation. This is what the class does. 
-}
class ToExprBase a where 
    toExprBase :: a -> Expression

{-|
    @Pattern@ on their own should be the minimal data type which a @toString@ function can be implemented.
    Thus, we need a way to convert enriched trees (i.e: tagged via the Cofree Comonad) to our
    fixed point representation. This is what the class does. 
-}
class ToPatternBase a where 
    toPatternBase :: a -> Pattern

{-|
    @Guard@ on their own should be the minimal data type which a @toString@ function can be implemented.
    Thus, we need a way to convert enriched trees (i.e: tagged via the Cofree Comonad) to our
    fixed point representation. This is what the class does. 
-}
class ToGuardBase a where 
    toGuardBase :: a -> Guard

instance (ToTypesBase typesA, ToPatternBase patternA, ToGuardBase guardA)
  => ToExprBase (Cofree (ExpressionF typesA patternA guardA) a) where 
  toExprBase (_ :< e) = toExprBase e
  
instance (ToTypesBase typesA, ToPatternBase patternA, ToGuardBase guardA)
  => ToExprBase
  ( ExpressionF
    typesA
    patternA
    guardA
    (Cofree (ExpressionF typesA patternA guardA) a)
  ) where 
  toExprBase e = Expression $ mapExpressionF toTypesBase toPatternBase undefined toExprBase e


instance ToTypesBase (Cofree TypesF a) where
  toTypesBase (_ :< t) = toTypesBase t

instance ToPatternBase (PatternF (Cofree PatternF a)) where
  toPatternBase p = Fix $ toPatternBase <$> p
instance ToPatternBase (Cofree PatternF a) where
  toPatternBase (_ :< p) = toPatternBase p

instance (ToPatternBase patternA, ToExprBase expressionA) 
  => ToGuardBase (GuardF patternA expressionA (Cofree (GuardF patternA expressionA) a)) where
  toGuardBase g = Guard $ mapGuardF toPatternBase toExprBase (const ()) g

