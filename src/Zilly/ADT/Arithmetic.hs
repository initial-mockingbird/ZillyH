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
{-# LANGUAGE TypeOperators         #-}

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
module Zilly.ADT.Arithmetic where

import Zilly.Types
import Data.Kind (Type)
import Zilly.UpcastPlus
import Data.Singletons (SingI)
{-| Zilly expression Language. |-}
data  Arithmetic   
  (sup :: Types -> Type)  -- | Parent Type
  (sub :: Types -> Type)  -- | Child Type
  (ctx :: Type)           --    | Allows for multiple interpretations
  (a :: Types)            -- | Expression type
  where
  Plus     :: PlusX   sup sub ctx a b c -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx b -> Arithmetic sup sub ctx c
  Minus    :: MinusX  sup sub ctx a b c -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx b -> Arithmetic sup sub ctx c
  Times    :: TimesX  sup sub ctx a b c -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx b -> Arithmetic sup sub ctx c
  Div      :: DivX    sup sub ctx a b c -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx b -> Arithmetic sup sub ctx c
  Mod      :: ModX    sup sub ctx a b c -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx b -> Arithmetic sup sub ctx c
  Power    :: PowerX  sup sub ctx a b c -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx b -> Arithmetic sup sub ctx c
  UMinus   :: UMinusX sup sub ctx a     -> Arithmetic sup sub ctx a -> Arithmetic sup sub ctx a
  ArithExp :: ArithExpX sup sub ctx a   -> Arithmetic sup sub ctx a 
  ArithInh :: ArithInhX sup sub ctx a   -> Arithmetic sup sub ctx a 
  ArithUpcasted :: ArithUpcastedX sup sub ctx a b -> Arithmetic sup sub ctx a ->  Arithmetic sup sub ctx b 

type family PlusX   (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family MinusX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family TimesX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family DivX    (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family ModX    (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family PowerX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family ArithUpcastedX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) :: Type

type family UMinusX (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ArithExpX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ArithInhX  (sup :: Types -> Type) (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type

