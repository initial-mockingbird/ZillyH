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
module Zilly.Upcast where
  
import Zilly.RValue
import Zilly.ADT.Expression
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

upcastable :: forall (a :: Types) (b :: Types) ctx. 
  ( SingI a
  , SingI b
  , forall (a :: Types).  RValue ctx (Lazy (Lazy a)) 
  , forall (a :: Types0). RValue ctx (Lazy (Value a)) 
  , forall (a :: Types0). RValue ctx (Value a) 
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
            -> withRVType @ctx  (sing @a)
            $  rvalueIsPred @a
            $  withSingI sub 
            $  SomethingElseUBN @a @b
      SNothing  -> NonExistentUB

type family UpcastX  (ctx :: Type) (a :: Types) (b :: Types) :: Type

class Upcast ctx where
  upcast :: forall (a :: Types) (b :: Types)
    . UpcastX ctx a b -> E ctx a  -> UpperBoundResults (E ctx) a b
