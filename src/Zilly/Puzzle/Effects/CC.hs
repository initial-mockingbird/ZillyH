module Zilly.Puzzle.Effects.CC where

class Monad m => MonadCC m where
  getCC :: m Int
  cycleCC :: m ()
