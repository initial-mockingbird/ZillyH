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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

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
module Zilly.ADT.Comparison where

import Zilly.Types
import Data.Kind (Type)

{-| Zilly expression Language. |-}
data  Comparison (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) where
  LT   :: LTX    f ctx a b c -> f ctx a -> f ctx b -> Comparison f ctx c
  LTEQ :: LTEQX  f ctx a b c -> f ctx a -> f ctx b -> Comparison f ctx c
  GT   :: GTX    f ctx a b c -> f ctx a -> f ctx b -> Comparison f ctx c
  GTEQ :: GTEQX  f ctx a b c -> f ctx a -> f ctx b -> Comparison f ctx c
  EQ   :: EQX    f ctx a b c -> f ctx a -> f ctx b -> Comparison f ctx c
  NEQ  :: NEQX   f ctx a b c -> f ctx a -> f ctx b -> Comparison f ctx c
  ComparisonExp :: ComparisonExpX f ctx a          -> Comparison f ctx a
  ComparisonInh :: ComparisonInhX f ctx a -> f ctx a       -> Comparison f ctx a

type family LTX   (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family LTEQX (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family GTX   (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family GTEQX (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family EQX   (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family NEQX  (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) (c :: Types) :: Type
type family ComparisonExpX  (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ComparisonInhX  (f :: Type -> Types -> Type) (ctx :: Type) (a :: Types) :: Type
