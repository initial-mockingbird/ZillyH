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
{-# LANGUAGE ImportQualifiedPost   #-}
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
module Zilly.ADT.Array where

import Zilly.Types qualified as ZT
import Data.Kind (Type)
import Data.Sequence

{-| Zilly expression Language. |-}
data  ArrayE 
  (sup :: ZT.Types -> Type)  -- | Parent Type
  (sub :: ZT.Types -> Type)  -- | Child Type
  (ctx :: Type)           --    | Allows for multiple interpretations
  (a :: ZT.Types)            -- | Expression type
  where
  ArrayLiteral :: ArrayLiteralX sup sub ctx a 
    -> Seq (ArrayE sup sub ctx a)
    -> ArrayE sup sub ctx (ZT.Array a)
  ArrayIndex   :: ArrayIndexX sup sub ctx a 
    -> ArrayE sup sub ctx (ZT.Array a) 
    -> ArrayE sup sub ctx (ZT.Value ZT.Z)
    -> ArrayE sup sub ctx a 
  ArrayExp     :: ArrayExpX sup sub ctx a  
    -> ArrayE sup sub ctx a
  ArrayInh     :: ArrayInhX sup sub ctx a
    -> ArrayE sup sub ctx a

type family ArrayLiteralX (sup :: ZT.Types -> Type) (sub :: ZT.Types -> Type) (ctx :: Type) (a :: ZT.Types) :: Type
type family ArrayIndexX   (sup :: ZT.Types -> Type) (sub :: ZT.Types -> Type) (ctx :: Type) (a :: ZT.Types) :: Type
type family ArrayExpX     (sup :: ZT.Types -> Type) (sub :: ZT.Types -> Type) (ctx :: Type) (a :: ZT.Types) :: Type
type family ArrayInhX     (sup :: ZT.Types -> Type) (sub :: ZT.Types -> Type) (ctx :: Type) (a :: ZT.Types) :: Type



