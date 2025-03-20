{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE PackageImports             #-}
module Classic.Parser.QuickCheck where

import Debug.Trace (trace)
import Zilly.ADT.Expression
import Test.Framework.QuickCheckWrapper
import Text.Parsec.Pos
import Data.Coerce (coerce)
import Control.Monad