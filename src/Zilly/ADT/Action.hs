{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module      : Zilly.ADT.Expression
Description : Main Action  Tree for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

TODO: adapt it to fit trees that grow.

-}
module Zilly.ADT.Action where

import Utilities.LensM
import Zilly.ADT.Expression
import Zilly.Classic.Expression
import Zilly.Types
import Zilly.RValue
import Zilly.Upcast
import Zilly.Classic.Interpreter
import Utilities.TypedMap
import Utilities.ShowM
import Control.Monad.Reader

import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad
import Data.Singletons (SingI)
import Debug.Trace (trace)
import Control.Applicative (Alternative)
import Data.Singletons (SingI(..))


type family AssocActionTag (ctx :: Type) :: Type

infix 0 :=
infix 0 :=.
data A ctx r where
  (:=) :: forall {m} {env} {ctx} actx (var :: Types) (e :: Types) .
    ( AssocActionTag actx ~ ctx
    , AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    , SingI var
    , SingI e
    , RValue ctx var
    , RValue ctx e
    , UpperBound var  e ~ Just var
    ) 
    =>  LensM m (E ctx var) -> E ctx e -> A actx '()
  (:=.) :: forall {m} {env} {ctx} actx (var :: Types) (e :: Types) .
    ( AssocActionTag actx ~ ctx
    , AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    , SingI var
    , SingI e
    , RValue ctx var
    , RValue ctx e
    , UpperBound var (RValueT e) ~ Just var
    ) 
    =>  LensM m (E ctx var) -> E ctx  e -> A actx '()
  Print :: forall {ctx} actx a.
    ( AssocActionTag actx ~ ctx
    , SingI a
    , RValue ctx a
    )
    => E ctx a -> A actx '()
  OfExpr :: forall {ctx} actx a.
    ( AssocActionTag actx ~ ctx
    , SingI a
    , RValue ctx a
    )
    => E ctx a -> A actx '()


class Execute actx where
  execInstruction :: forall {ctx} {m} {env} a. 
    ( AssocActionTag actx ~ ctx
    , AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    ) => A actx a -> m (A actx a, env)

  
