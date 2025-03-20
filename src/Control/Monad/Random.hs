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

class Monad m => MonadRandom m where 
  randInt :: Int -> m Int



newtype RandomT m a = RandomT {runRandomT :: StateT Int m a} 
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadFail, Alternative, MonadPlus ) 

instance Monad m => MonadRandom (RandomT m) where 
  randInt ub = RandomT $ do 
    n <- get 
    trace (show n) $ pure ()
    let n' = (ub * 41 + n) `mod` 1697
    put n'
    pure n'


instance MonadReader r m => MonadReader r (RandomT m)  where 
  local f (RandomT a) = RandomT $ local f a
  ask  = RandomT $ ask 
  reader f = RandomT $ reader f

evalRandomIO :: MonadIO m => Int -> RandomT m a -> m a
evalRandomIO n (RandomT f) = evalStateT f n


runRandomIO :: Int -> RandomT m a -> m (a,Int)
runRandomIO n (RandomT f) = runStateT f n
