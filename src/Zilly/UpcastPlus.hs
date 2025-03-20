{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
Module      : Zilly.Upcast
Description : Defines utilities to upcasting expressions
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Zilly.UpcastPlus where

import Data.Proof
import Zilly.RValuePlus
import Zilly.ADT.ExpressionPlus
import Zilly.Types
import Utilities.LensM
import Control.Applicative (Const(..))
import Prelude.Singletons hiding (Const(..))
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Data.Singletons.Decide

---------------------
-- Upcasting
---------------------

data UpperBoundResults f a b where
  NonExistentUB   :: (UpperBound a b ~ Nothing) => UpperBoundResults f a b 
  SameTypeUB      :: (a ~ b, UpperBound a b ~ Just a) => f a -> UpperBoundResults f a b 
  LeftUB          :: (UpperBound a b ~ Just a)  => f a -> UpperBoundResults f a b 
  RightUB         :: (UpperBound a b ~ Just b)  => f b -> UpperBoundResults f a b 
  SomethingElseUB :: forall {r :: Types} f (a :: Types) (b :: Types) . 
    ( UpperBound a b ~ Just r
    , SingI r
    ) => f r -> UpperBoundResults f a b 

instance Semigroup (UpperBoundResults f a b) where
  NonExistentUB <> _ = NonExistentUB 
  _ <> NonExistentUB = NonExistentUB 
  SomethingElseUB _ <> a = a
  a <> SomethingElseUB _ = a
  LeftUB a <> RightUB _  = SameTypeUB a
  RightUB a <> LeftUB _  = SameTypeUB a
  SameTypeUB a <> _      = SameTypeUB a
  _ <> SameTypeUB a      = SameTypeUB a
  LeftUB a <> LeftUB _   = LeftUB a
  RightUB a <> RightUB _ = RightUB a
  

pattern SameTypeUBN ::  (a ~ b, UpperBound a b ~ Just a) => UpperBoundResults (Const ()) a b 
pattern SameTypeUBN = SameTypeUB (Const ())
  

pattern LeftUBN ::  (UpperBound a b ~ Just a) => UpperBoundResults (Const ()) a b 
pattern LeftUBN = LeftUB (Const ())

pattern RightUBN ::  (UpperBound a b ~ Just b) => UpperBoundResults (Const ()) a b 
pattern RightUBN = RightUB (Const ())

pattern SomethingElseUBN :: 
  ( UpperBound a b ~ Just r
  , SingI r
  ) => UpperBoundResults (Const ()) a b 
pattern SomethingElseUBN = SomethingElseUB (Const ())

upcastable 
  :: forall 
    (a :: Types) 
    (b :: Types) 
    (f   :: (Types -> Type) -> (Types -> Type) -> Type -> Types -> Type)
    (sup :: Types -> Type)
    (sub :: Types -> Type)
    (ctx :: Type) . 
  ( SingI a
  , SingI b
  , TypesCaseAnalysis (RValue (f sup sub ctx))
  --, forall (a :: Types).  RValue (f sup sub ctx)  a
  ) => UpperBoundResults (Const ()) a b
upcastable 
  = withSingIUBType @a @b 
  $ case decideEquality (sing @a) (sing @b) of
    Just Refl -> ubIsIdempotent @a $ SameTypeUBN
    Nothing -> case sing @(UpperBound a b) of
      SJust sub -> case decideEquality (sing @a) sub of
        Just Refl -> LeftUBN
        Nothing   -> case decideEquality (sing @b) sub of
          Just Refl -> RightUBN
          Nothing   
            -> withRVType @(f sup sub ctx)  (sing @a)
            $  rvalueIsPred @a
            $  withSingI sub 
            $  SomethingElseUBN @a @b
      SNothing  -> NonExistentUB

type family UpcastX  
  (f   :: Types -> Type )
  (a :: Types) 
  :: Type
type family UpcastCtx f     :: Type
type family UpcastSup f     :: (Types -> Type)
type family UpcastSub f     :: (Types -> Type)
type family UpcastSupCtx f  :: Type
type family UpcastSubCtx f  :: Type

class Upcast (f :: Types -> Type) where
  upcast :: forall (a :: Types) (b :: Types)  
    . (SingI a, SingI b) => UpcastX f a  -> f a  -> UpperBoundResults f  a b
