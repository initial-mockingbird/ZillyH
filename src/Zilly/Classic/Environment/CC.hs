{-# LANGUAGE ImportQualifiedPost #-}
module Zilly.Classic.Environment.CC where

import Data.Map (Map)
import Data.Map qualified as M 


data CCState  = CCState 
  { lastEvaluated :: !Int  
  }

newtype CCenv = CCenv (Map String CCState )





