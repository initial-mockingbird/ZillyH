{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
module Zilly.ZillyPlus.Interpreter where


import Utilities.TypedMapPlus
import Utilities.LensM
import Zilly.RValuePlus
import Zilly.Types

import Control.Monad.Reader


import Control.Monad
import Control.Applicative (Alternative)
import Zilly.ADT.ExpressionPlus

newtype TaggedInterpreter ctx a = TI { runTI :: ReaderT (Gamma (AssocCtxMonad ctx)) IO a} 
  deriving newtype 
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadFail
    )

instance 
  ( Gamma (AssocCtxMonad ctx) ~ TypeRepMap sub ctx
  ) =>  MonadReader (TypeRepMap sub ctx) (TaggedInterpreter ctx) where
  ask = TI ask
  local f = TI . local f . runTI

runTaggedInterpreter :: Gamma (AssocCtxMonad ctx) -> TaggedInterpreter ctx a ->  IO a
runTaggedInterpreter env = flip runReaderT env . runTI

{- 


run :: BaseInterpreter a -> IO a
run = flip runReaderT  env . runBI
  where
    {- !env = insert "x" (35  :: Value Int) 
        $ insert "y" (5000 :: Value Int)
        $ insert "z" (13 :: Value Int)
        $ empty -}
    env = empty

printProgram :: ShowM BaseInterpreter a => a -> IO ()
printProgram = putStrLn <=< run . showM 

printAndExec :: Traversable t => t (A (TypeRepMap BaseInterpreter ExprTag) BaseInterpreter a) -> IO ()
printAndExec = run . execProgram -}
