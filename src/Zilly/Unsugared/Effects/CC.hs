{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Zilly.Unsugared.Effects.CC where

import Control.Monad.State
import Control.Monad.Trans.Class
import Control.Applicative
import Control.Monad.Reader

newtype CCStateT m a  = CCStateT { _runCCStateT :: StateT Int m a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadState Int
    , MonadIO
    , Alternative
    , MonadFail
    )


evalCCStateT :: Monad m => Int -> CCStateT m a -> m a
evalCCStateT i (CCStateT m) = evalStateT m i

runCCStateT :: Int -> CCStateT m a -> m (a, Int)
runCCStateT i (CCStateT m) = runStateT m i

class Monad m => MonadCC m where
  getCC :: m Int
  cycleCC :: m ()

instance Monad m => MonadCC (CCStateT m) where
  getCC = get
  cycleCC = modify (+1)

instance MonadTrans CCStateT where
  lift = CCStateT . lift

instance MonadReader r m => MonadReader r (CCStateT m) where
  local f (CCStateT m) = CCStateT $ local f m
  ask  = CCStateT $ ask
  reader f = CCStateT $ reader f
