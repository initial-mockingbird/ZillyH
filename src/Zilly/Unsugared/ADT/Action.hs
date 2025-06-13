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

module Zilly.Unsugared.ADT.Action where

import Zilly.Unsugared.ADT.Expression
import Zilly.Unsugared.Newtypes
import Zilly.Unsugared.Environment.TypedMap
import Zilly.Unsugared.Effects.CC
import Data.Kind (Type)
import Prelude.Singletons (SingI(..),demote)
import Control.Monad.Reader
import Data.Singletons.Decide
import Debug.Trace (trace)
import Data.Default
import Control.Monad.Error.Class
import Zilly.Unsugared.Effects.Block (CCActions(..))


type AEffects m =
  ( Effects m
  , MonadCC m
  , CCActions m
  , Default (m (TypeRepMap (E m)))
  )

data A (m :: Type -> Type) where
  Assign   :: SingI ltype => LensM (E m) ltype -> E m ltype -> A m
  Reassign :: SingI ltype => LensM (E m) ltype -> E m ltype -> A m
  Print    :: SingI a => E m a -> A m
  SysCommand :: String -> A m
  ABottom  :: A m


evalA' :: forall m.
  ( AEffects m
  )
  => A m -> m (TypeRepMap (E m), A m)
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
    env <- getEnv @(E m)
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



evalA :: forall m. (Effects m, Default (m (TypeRepMap (E m))))
  => A m -> m (TypeRepMap (E m), A m)
evalA (Print a) = evalE a >>= \case
  MkSomeExpression a' -> getEnv >>= \env -> pure  (env, Print a')
evalA a@(Assign @ltype x y) = withSingIFtype @ltype $ do
  env1' <- getEnv
  -- env1' <- declare @(Ftype ltype) (varNameM x) env0
  withEnv @(E m) env1' $ evalE y >>= \case
    MkSomeExpression @a' a'
      -> withSingIFtype @ltype
      $ case upcastable @(Ftype ltype) @a' of
        SameTypeUB _ -> do
          env <- getEnv
          (\env' -> (env',a)) <$> setM x a' env
        LeftUB _
          -> eqWeakening @(UpperBound (Ftype ltype) a') @(Just (Ftype ltype))
          $ do
            env <- getEnv
            (\env' -> (env',a)) <$> setM x (Subtyped @(Ftype ltype) a') env
        _ -> error "error evaling assignment. Type Mismatch"
evalA a@(Reassign @ltype x y) = evalE y >>= \case
  MkSomeExpression @a' a'
    -> withSingIFtype @ltype
    $ case upcastable @(Ftype ltype) @a' of
      SameTypeUB _ -> do
        env <- getEnv
        (\env' -> (env',a)) <$> setM x a' env
      LeftUB _
        -> eqWeakening @(UpperBound (Ftype ltype) a') @(Just (Ftype ltype))
        $ do
          env <- getEnv
          (\env' -> (env',a)) <$> setM x (Subtyped @(Ftype ltype) a') env
      _ -> error "error evaling reassignment. Type Mismatch"

evalA a@(SysCommand "reset") = do
  env <- def @(m (TypeRepMap (E m)))
  pure  (env,a)
evalA (SysCommand _) = evalA ABottom
evalA ABottom = error "trying to eval action bottom"

evalProgram :: forall m. (Effects m, Default (m (TypeRepMap (E m))))
  => [A m] -> m (Either GammaErrors (TypeRepMap (E m) ,[A m]))
evalProgram []     = getEnv >>= \env -> pure (Right (env, []))
evalProgram (x:xs) = evalA @m x >>= \(env',x') -> (fmap . fmap) (x' :) <$> withEnv env' (evalProgram xs)

instance Show (A m) where
  showsPrec _ = \case
    (Assign @ltype x e)
      -> shows (demote @ltype)
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
    ABottom -> showString "ABOTTOM"
