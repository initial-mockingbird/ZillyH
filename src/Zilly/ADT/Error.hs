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
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}

{-|
Module      : Zilly.ADT.Expression
Description : Main Expression Tree a la Trees that grow for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX
Check
@@
@article{najd2016trees,
  title={Trees that grow},
  author={Najd, Shayan and Jones, Simon Peyton},
  journal={arXiv preprint arXiv:1610.04799},
  year={2016}
}
@@
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf

-}
module Zilly.ADT.Error where

import Zilly.Types
import Data.Kind (Type)

{-| Zilly expression Language. |-}
data  Error 
  (sup :: Types -> Type)  -- | Parent Type
  (sub :: Types -> Type)  -- | Child Type
  (ctx :: Type)           -- | Allows for multiple interpretations
  (a :: Types)            -- | Expression type
  where
  ErrorLiteral :: ErrorLiteralX sup sub ctx a -> String -> Error sup sub ctx a
  ErrorExp     :: ErrorExpX sup sub ctx a -> Error sup sub ctx a 
  ErrorInh     :: ErrorInhX sup sub ctx a -> Error sup sub ctx a 

type family ErrorLiteralX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ErrorExpX      (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ErrorInhX      (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type


