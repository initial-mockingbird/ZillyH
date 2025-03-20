{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PolyKinds             #-}
module Data.Proof where

import Data.Function.Singletons
import Data.Kind (Type, Constraint)
import Utilities.ShowM

data Void2 a

instance Functor m => ShowM m (Void2 a)


class (forall (a :: k). psi  a) => C0 (psi :: k -> Constraint)  
instance (forall (a :: k). psi a) => C0 (psi :: k -> Constraint) 




class (forall (a :: k0). psi (f a)) => C (psi :: k1 -> Constraint) (f :: k0 -> k1) 
instance (forall (a :: k0). psi (f a)) => C (psi :: k1 -> Constraint) (f :: k0 -> k1)

class (forall a. psi (f $ a)) => CS psi f 
instance (forall a. psi (f $ a)) => CS psi f

class (forall (a :: k0). psi (f a) (g a)) 
  => C2 (psi :: k1 -> k2 -> Constraint) (f :: k0 -> k1) (g :: k0 -> k2) 
instance (forall (a :: k0). psi (f a) (g a)) 
  => C2 (psi :: k1 -> k2 -> Constraint) (f :: k0 -> k1) (g :: k0 -> k2)


data Dict (c :: Constraint) where 
  Dict :: c => Dict c
