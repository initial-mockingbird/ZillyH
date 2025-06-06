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

data A (m :: Type -> Type) where
  Assign   :: SingI ltype => LensM (E m) ltype -> E m ltype -> A m
  Reassign :: SingI ltype => LensM (E m) ltype -> E m ltype -> A m
  Print    :: SingI a => E m a -> A m
  SysCommand :: String -> A m
  ABottom  :: A m

evalA :: forall m. (Effects m, Default (m (TypeRepMap (E m))))
  => A m -> m (Either GammaErrors (TypeRepMap (E m), A m))
evalA (Print a) = cycleCC >>   evalE a >>= \case
  MkSomeExpression a' -> ask >>= \env -> (pure . pure) (env, Print a')
evalA a@(Assign @ltype x y) = withSingIFtype @ltype $ cycleCC >> do
  env0 <- ask
  env1 <- declare @(Ftype ltype) (varNameM x) env0
  case env1 of
    Left _ -> error "error evaling assignment. Variable Already Declared"
    Right env1' -> local (const env1') $ evalE y >>= \case
        MkSomeExpression @a' a'
          -> withSingIFtype @ltype
          $ case upcastable @(Ftype ltype) @a' of
            SameTypeUB _ -> do
              env <- ask
              fmap (\env' -> (env',a)) <$> setM x a' env
            LeftUB _
              -> eqWeakening @(UpperBound (Ftype ltype) a') @(Just (Ftype ltype))
              $ do
                env <- ask
                fmap (\env' -> (env',a)) <$> setM x (Subtyped @(Ftype ltype) a') env
            _ -> error "error evaling assignment. Type Mismatch"
evalA a@(Reassign @ltype x y) = cycleCC >> evalE y >>= \case
  MkSomeExpression @a' a'
    -> withSingIFtype @ltype
    $ case upcastable @(Ftype ltype) @a' of
      SameTypeUB _ -> do
        env <- ask
        fmap (\env' -> (env',a)) <$> setM x a' env
      LeftUB _
        -> eqWeakening @(UpperBound (Ftype ltype) a') @(Just (Ftype ltype))
        $ do
          env <- ask
          fmap (\env' -> (env',a)) <$> setM x (Subtyped @(Ftype ltype) a') env
      _ -> error "error evaling reassignment. Type Mismatch"

evalA a@(SysCommand "reset") = do
  env <- def @(m (TypeRepMap (E m)))
  pure $ Right (env,a)
evalA (SysCommand _) = evalA ABottom
evalA ABottom = error "trying to eval action bottom"

evalProgram :: forall m. (Effects m, Default (m (TypeRepMap (E m))))
  => [A m] -> m (Either GammaErrors (TypeRepMap (E m) ,[A m]))
evalProgram []     = ask >>= \env -> pure (Right (env, []))
evalProgram (x:xs) = evalA @m x >>= \case
  (Left err) -> pure (Left err)
  (Right (env',x')) -> (fmap . fmap) (x' :) <$> local (const env') (evalProgram xs)

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
