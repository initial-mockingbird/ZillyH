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
module Zilly.ADT.ExpressionPlus where

import Data.Proof
import Zilly.Types
import Utilities.LensM
import Data.Kind (Type)

type family AssocCtxMonad (ctx :: Type) :: (Type -> Type)



{-| Zilly expression Language. |-}
data  E 
  (sup :: Types -> Type)  -- | Parent Type
  (sub :: Types -> Type)  -- | Child Type
  (ctx :: Type)           -- | Allows for multiple interpretations
  (a :: Types)            -- | Expression type
  where                  
  Val      :: ValX sub ctx a          -> E Void2 sub ctx a
  Var      :: VarX sub ctx a          -> LensM (AssocCtxMonad ctx) (E Void2 sub ctx a) -> E Void2 sub ctx a
  If       :: IfX sub ctx x0 x1 x2 x3 -> E Void2 sub ctx x0 -> E Void2 sub ctx x1 -> E Void2 sub ctx x2 -> E Void2 sub ctx x3
  Lambda   :: LambdaX sub ctx a b     -> Maybe (LensM (AssocCtxMonad ctx) (E Void2 sub ctx a)) -> E Void2 sub ctx b  -> E Void2 sub ctx (a ~> b)
  Defer    :: DeferX sub ctx a        -> E Void2 sub ctx a -> E Void2 sub ctx (Lazy a)
  Formula  :: FormulaX sub ctx a      -> LensM (AssocCtxMonad ctx) (E Void2 sub ctx a) -> E Void2 sub ctx (Lazy a)
  Closure  :: ClosureX sub ctx a      -> (E Void2 sub ctx a,Gamma (AssocCtxMonad ctx)) -> E Void2 sub ctx a
  LambdaC  :: LambdaCX sub ctx a b    -> (Gamma (AssocCtxMonad ctx), Maybe (LensM (AssocCtxMonad ctx) (E Void2 sub ctx a)), E Void2 sub ctx b) -> E Void2 sub ctx (a ~> b)
  ValueC   :: ValueCX sub ctx a       -> Gamma (AssocCtxMonad ctx) -> E Void2 sub ctx a
  Subtyped :: SubtypedX sub ctx a b   -> E Void2 sub ctx a -> E Void2 sub ctx b
  App      :: forall ctx sub f x b arg. AppX sub ctx f x arg b -> E Void2 sub ctx f -> E Void2 sub ctx x -> E Void2 sub ctx b
  Exp      :: ExpX sub ctx a      -> E Void2 sub ctx a


type family ValX      (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family ValueCX   (sub :: Types -> Type) (ctx :: Type) (a :: Types):: Type
type family ClosureX  (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family VarX      (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family DeferX    (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family FormulaX  (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type
type family LambdaCX  (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) :: Type
type family SubtypedX (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) :: Type
type family LambdaX   (sub :: Types -> Type) (ctx :: Type) (a :: Types) (b :: Types) :: Type
type family AppX      (sub :: Types -> Type) (ctx :: Type) (f :: Types ) (x :: Types ) (arg :: Types) (b :: Types ) :: Type
type family IfX       (sub :: Types -> Type) (ctx :: Type) (x0 :: Types) (x1 :: Types) (x2 :: Types ) (x3 :: Types) :: Type
type family ExpX      (sub :: Types -> Type) (ctx :: Type) (a :: Types) :: Type


