{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}

module Zilly.Puzzle.ADT.Action where

import Zilly.Puzzle.ADT.Expression
import Zilly.Puzzle.Newtypes
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Effects.CC
import Data.Kind (Type)
import Control.Monad.Reader
import Debug.Trace (trace)
import Data.Default
import Control.Monad.Error.Class
import Zilly.Puzzle.Effects.Block (CCActions(..))


type AEffects m =
  ( Effects m
  , MonadCC m
  , CCActions m
  -- , CCActions m
  )

type ACtxConstraint ctx m =
  ( CtxConstraint ctx m
  , AEffects m
  , Default (m (TypeRepMap (E ctx)))

  )

data A (ctx :: Type) where
  Assign   :: Types -> LensM (E ctx) -> E ctx -> A ctx
  Reassign :: LensM (E ctx) -> E ctx -> A ctx
  Print    :: E ctx -> A ctx
  SysCommand :: String -> A ctx
  ABottom  :: A ctx


evalA' :: forall {m} ctx.
  ( ACtxConstraint ctx m
  )
  => A ctx -> m (TypeRepMap (E ctx), A ctx)
evalA' a = fmap (a,) getQ >>= \case
  (Print _, 0) -> do
    (env,result) <- evalA a
    pure (env, result)
  (Print _, 1) -> do
    cycleCC
    (env,result) <- evalA a
    putQ 0
    pure (env, result)

  (Reassign {},0) -> do
    (env, result) <- evalA a
    cycleCC
    putQ 0
    pure (env, result)
  (Reassign {},1) -> do
    cycleCC
    (env, result) <- evalA a
    cycleCC
    putQ 0
    pure (env, result )
  (SysCommand "tick", _) -> do
    cycleCC
    putQ 0
    env <- getEnv @(E ctx)
    pure (env, a)
  (SysCommand "reset", _) -> do
    res <- evalA a
    cycleCC
    putQ 0
    pure res

  (Assign {}, _) -> do
    (env, a') <- evalA a
    putQ 1
    pure (env,a')
  _ -> evalA a



evalA :: forall {m} ctx.
  (ACtxConstraint ctx m)
  => A ctx -> m (TypeRepMap (E ctx), A ctx)
evalA (Print a) = evalE @ctx a >>= \case
  a' -> getEnv >>= \env -> pure  (env, Print a')
evalA a@(Assign ltype x y) = do
  env1' <- getEnv
  -- env1' <- declare @(Ftype ltype) (varNameM x) env0
  withEnv @(E ctx) env1' $ evalE y >>= \a' -> do
      env <- getEnv
      (\env' -> (env',a)) <$> setM x a' ltype env

evalA a@(Reassign x y) = evalE y >>= \a' -> do
  env <- getEnv
  md <- varMetadata x env
  (\env' -> (env',a)) <$> setM x a' md env

evalA a@(SysCommand "reset") = do
  env <- def @(m (TypeRepMap (E ctx)))
  pure  (env,a)
evalA (SysCommand _) = evalA ABottom
evalA ABottom = error "trying to eval action bottom"

evalProgram :: forall {m} ctx.
  ( ACtxConstraint ctx m
  )
  => [A ctx] -> m ((TypeRepMap (E ctx) ,[A ctx]))
evalProgram []     = getEnv >>= \env -> pure ((env, []))
evalProgram (x:xs) = evalA' @ctx x >>= \(env',x') -> fmap (x' :) <$> withEnv env' (evalProgram xs)

instance
  ( CtxPureConstraint ctx
  , MonadIO (EvalMonad (E ctx))
  , MonadError String (EvalMonad (E ctx))
  ) => Show (A ctx) where
  showsPrec _ = \case
    (Assign t x e)
      -> shows t
      . showString " "
      . shows (UT $ varNameM x)
      . showString " := "
      . shows e
      . showString ";"
    (Reassign  x e)
      -> shows (UT $ varNameM x)
      . showString " := "
      . shows e
      . showString ";"
    (Print e) -> shows e
    (SysCommand s) -> showString "sys." . showString s . showString "();"
    ABottom -> showString "⊥"
