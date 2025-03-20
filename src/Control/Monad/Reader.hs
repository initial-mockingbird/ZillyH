{-# LANGUAGE PackageImports #-}
module Control.Monad.Reader 
  ( module R
  , localM
  ) where

import qualified "mtl" Control.Monad.Reader as R
import "mtl" Control.Monad.Reader 


localM :: (MonadReader env m) => (env -> m env) -> m a -> m a
localM f m = do
  env <- ask >>= f
  local (const env) m