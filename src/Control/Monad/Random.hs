{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Control.Monad.Random where

import Control.Monad
import Control.Monad.State
import Control.Applicative
import Control.Monad.Reader
import Debug.Trace
import Control.Monad.Trans.Class

class Monad m => MonadRandom m where
  randInt :: Int -> m Int



newtype RandomT m a = RandomT {runRandomT :: StateT Float m a}
  deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadIO
    , MonadFail
    , Alternative
    , MonadPlus
    )

instance Monad m => MonadRandom (RandomT m) where
  randInt ub = RandomT $ do
    n <- get
    -- new_seed = sem * 997 - floor(sem * 997)
    -- num = floor(new_seed *) mod n
    -- num = floor(new_seed * n)
    --let n' = (ub * 41 + n) `mod` 1697
    let n' = n * 997 - (fromInteger . floor) (n * 997)
    put n'
    pure . max 0 . floor $ fromIntegral ub * n'


instance MonadReader r m => MonadReader r (RandomT m)  where
  local f (RandomT a) = RandomT $ local f a
  ask  = RandomT $ ask
  reader f = RandomT $ reader f

instance MonadTrans RandomT where
  lift = RandomT . lift

evalRandomIO :: MonadIO m => Float -> RandomT m a -> m a
evalRandomIO n (RandomT f) = evalStateT f n


runRandomIO :: Float -> RandomT m a -> m (a,Float)
runRandomIO n (RandomT f) = runStateT f n
