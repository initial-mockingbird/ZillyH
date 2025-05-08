{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Matchers where

import Data.Kind (Type)
import Prelude.Singletons
import Data.Singletons.Decide
import GHC.TypeLits.Singletons
import GHC.TypeLits

class Matchable (k :: Type) where
  match :: forall (a :: k) (b :: k). SingI a => Sing b -> Maybe (b :~: a)

instance Matchable Symbol where
  match :: forall (a :: Symbol) (b :: Symbol). SingI a => Sing b -> Maybe (b :~: a)
  match b@SSymbol = case sing @a of
    SSymbol -> sameSymbol b (SSymbol @a)

instance Matchable Natural where
  match :: forall (a :: Nat) (b :: Nat). SingI a => Sing b -> Maybe (b :~: a)
  match b@SNat = case sing @a of
    SNat -> sameNat b (SNat @a)

matches :: forall {k} (a :: k) (b :: k).
  (Matchable k, SingI a) => Sing b -> Maybe (b :~: a)
matches = match @k

withSucc :: forall n k. SingI n => (SingI (n Prelude.Singletons.+ 1) => k) -> k
withSucc f = case sing @n of
  SNat -> case sing @n %+ sing @1 of
    SNat -> f

-- class Satisfies (k :: Type) where
--   satisfies :: forall {a1 :: k} (a :: k).
--     SingI a => Sing (TyFun a1 Bool) -> Maybe (TyFun a )
