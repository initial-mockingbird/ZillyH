{-# OPTIONS_GHC -Wno-orphans #-}

{-|
Module      : Lilly.Parser.New.Definitions.Orphans 
Description : Orphan instances for Parser Definitions.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

To avoid clouting the definition module with utility instances that are only useful
for re-creating the fixpoint represantation. We dump them here. 
-}
module Lilly.Parser.New.Definitions.Orphans where

import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Definitions.Definitions
import Lilly.Parser.New.Definitions.Utilities
import Control.Comonad.Cofree
import Data.Fix 
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

