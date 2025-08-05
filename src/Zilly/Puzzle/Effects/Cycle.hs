module Zilly.Puzzle.Effects.Cycle where

import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Data.Functor (void)

data VisitedColor
  = White
  | Gray
  | Black

data VisitedStatus = VisitedStatus
  { wasVisited :: MVar VisitedColor
  }

mkVisitedStatus :: MonadIO m => m VisitedStatus
mkVisitedStatus = do
  mvar <- liftIO $ newMVar White
  pure $ VisitedStatus mvar

markVisited :: MonadIO m => VisitedStatus -> m ()
markVisited (VisitedStatus mvar) = do
  void . liftIO $ swapMVar mvar Gray

markFinished :: MonadIO m => VisitedStatus -> m ()
markFinished (VisitedStatus mvar) = do
  void . liftIO $ swapMVar mvar Black

exploreCycle :: MonadIO m => VisitedStatus -> m a -> m (Maybe a)
exploreCycle vs@(VisitedStatus mvar) action = do
  color <- liftIO $ readMVar mvar
  case color of
    White -> do
      markVisited vs
      result <- action
      markFinished vs
      pure $ Just result
    Gray -> do
      markFinished vs
      pure Nothing
    Black -> do
      markFinished vs
      pure Nothing
