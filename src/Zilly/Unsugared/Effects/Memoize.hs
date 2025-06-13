{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
module Zilly.Unsugared.Effects.Memoize where

import Zilly.Unsugared.Effects.CC
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Data.Functor (void)
import Debug.Trace (trace)
import Control.Monad.Error.Class

data Memoized m a = Memoized
  { refresh_condition    :: m Bool -- ^ True if we need to refresh the memoized val, false otherwise
  , memoized_val         :: MVar a -- ^ Memoized value, the mvar might be empty, in which case, we need to call refresh
  , refresh              :: m a -- ^ a way of getting a new value to be memoized
  }

mkMemoize :: MonadIO m => m Bool -> m a -> m (Memoized m a)
mkMemoize cond f = do
  mvar <- liftIO $ newEmptyMVar
  pure $ Memoized cond mvar f

runMemoized :: (MonadIO m) => Memoized m a -> m a
runMemoized (Memoized mrc mv r) = do
  rc <- liftA2 (||) mrc (liftIO $ isEmptyMVar mv)
  case rc of
    False -> liftIO $ readMVar mv
    True  -> do
      v <- r
      void $ liftIO $ tryTakeMVar mv
      liftIO $ putMVar mv v
      pure v

memoizeWithCC :: (MonadError String m, MonadIO m, MonadCC m) => m a -> m (Memoized m a)
memoizeWithCC f = do
  mvar <- liftIO $ newEmptyMVar
  cc <- getCC
  icycle <- liftIO $ newMVar cc
  l <- liftIO $ newMVar @Int (-1)
  let rc = do
        cc' <- getCC
        last_cycle <- liftIO $ readMVar icycle
        l' <- liftIO $ readMVar l
        case (cc' == last_cycle, cc' == l') of
          (True,_) -> pure False
          (False,False) ->  do
            pure True
          (False,True) -> do
            void $ liftIO $ swapMVar icycle cc'
            throwError "circular reference"
  let post = getCC >>= liftIO . swapMVar icycle
  let pre = getCC >>= liftIO . swapMVar l
  pure $ Memoized rc mvar (pre *> f <* post)
