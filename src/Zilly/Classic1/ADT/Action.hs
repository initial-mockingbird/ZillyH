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

module Zilly.Classic1.ADT.Action where

import Zilly.Classic1.ADT.Expression
import Zilly.Classic1.Newtypes
import Zilly.Classic1.Environment.TypedMap
import Data.Kind (Type)
import Prelude.Singletons (SingI(..),demote)
import Control.Monad.Reader
import Data.Singletons.Decide
import Debug.Trace (trace)

data A (m :: Type -> Type) where 
  Assign   :: SingI ltype => LensM (E m) ltype -> E m ltype -> A m
  Reassign :: SingI ltype => LensM (E m) ltype -> E m ltype -> A m
  Print    :: SingI a => E m a -> A m
  ABottom  :: A m

evalA :: Effects m => A m -> m (Either GammaErrors (TypeRepMap (E m), A m))
evalA (Print a) = evalE a >>= \case  
  MkSomeExpression a' -> ask >>= \env -> (pure . pure) (env, Print a')
evalA a@(Assign @ltype x y) = withSingIFtype @ltype $ do 
  liftIO . putStrLn $ "aqui"
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
evalA a@(Reassign @ltype x y) = evalE y >>= \case 
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

evalA ABottom = error "trying to eval action bottom" 

evalProgram :: forall m. Effects m => [A m] -> m (Either GammaErrors (TypeRepMap (E m) ,[A m]))
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
    ABottom -> showString "ABOTTOM"
