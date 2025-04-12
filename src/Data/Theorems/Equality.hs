{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Data.Theorems.Equality where
import Data.Kind (Type, Constraint)
import Prelude.Singletons
import Data.Proof
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)

class  EqClass (p :: TyFun k (k ~> Bool) -> Type) where
  eqSymmetry :: ((p $ a) $ b) :~: ((p $ b) $ a)
  eqReflexivity :: forall (a :: k).  ((p $ a) $ a) :~: True

  eqTransitivity :: forall (a :: k) (b :: k) (c :: k).
     ((p $ a) $ b) :~: True -> ((p $ b) $ c) :~: True -> ((p $ a) $ c) :~: True

  eqCast :: forall (a :: k) (b :: k) (c :: k).
    ((p $ a) $ b) :~: True -> a :~: b


trivialRefl :: () :~: ()
trivialRefl = Refl


instance EqClass (==@#@$) where

  eqSymmetry = unsafeCoerce Refl
  eqReflexivity = unsafeCoerce Refl
  eqTransitivity Refl Refl = unsafeCoerce Refl
  eqCast Refl = unsafeCoerce Refl
  {-# INLINE eqSymmetry #-}
  {-# INLINE eqReflexivity #-}
  {-# INLINE eqTransitivity #-}
  {-# INLINE eqCast #-}


class StrictPoset (p :: TyFun k (k ~> Bool) -> Type) where
  sPOIrreflexivity :: forall (a :: k).
    ((p $ a) $ a) :~: False
  sPOAsymmetry :: forall (a :: k) (b :: k).
    ((p $ a) $ b) :~: True -> ((p $ b) $ a) :~: False
  sPOTransitivity :: forall (a :: k) (b :: k) (c :: k).
    ((p $ a) $ b) :~: True -> ((p $ b) $ c) :~: True -> ((p $ a) $ c) :~: True

instance StrictPoset (<@#@$) where
  sPOIrreflexivity = unsafeCoerce Refl
  sPOAsymmetry Refl = unsafeCoerce Refl
  sPOTransitivity Refl Refl = unsafeCoerce Refl

  {-# INLINE sPOIrreflexivity #-}
  {-# INLINE sPOAsymmetry #-}
  {-# INLINE sPOTransitivity #-}

instance StrictPoset (>@#@$) where
  sPOIrreflexivity = unsafeCoerce Refl
  sPOAsymmetry Refl = unsafeCoerce Refl
  sPOTransitivity Refl Refl = unsafeCoerce Refl

  {-# INLINE sPOIrreflexivity #-}
  {-# INLINE sPOAsymmetry #-}
  {-# INLINE sPOTransitivity #-}



class Poset (p :: TyFun k (k ~> Bool) -> Type) where
  poReflexivity :: forall (a :: k).
    ((p $ a) $ a) :~: True
  poAntisymmetry :: forall (a :: k) (b :: k).
    ((p $ a) $ b) :~: True -> ((p $ b) $ a) :~: True -> a :~: b

  poTransitivity :: forall (a :: k) (b :: k) (c :: k).
    ((p $ a) $ b) :~: True -> ((p $ b) $ c) :~: True -> ((p $ a) $ c) :~: True


instance Poset (<=@#@$) where
  poReflexivity = unsafeCoerce Refl
  poAntisymmetry Refl Refl = unsafeCoerce Refl
  poTransitivity Refl Refl = unsafeCoerce Refl

  {-# INLINE poReflexivity #-}
  {-# INLINE poAntisymmetry #-}
  {-# INLINE poTransitivity #-}

instance Poset (>=@#@$) where
  poReflexivity = unsafeCoerce Refl
  poAntisymmetry Refl Refl = unsafeCoerce Refl
  poTransitivity Refl Refl = unsafeCoerce Refl

  {-# INLINE poReflexivity #-}
  {-# INLINE poAntisymmetry #-}
  {-# INLINE poTransitivity #-}



class Dual (p :: TyFun k (k ~> Bool) -> Type) (q :: TyFun k (k ~> Bool) -> Type) where
  dualI1 :: forall (a :: k) (b :: k).
    ((q $ a) $ b) :~: (Not ((p $ a) $ b) )
  dualI2 :: forall (a :: k) (b :: k).
    ((p $ a) $ b) :~: (Not ((q $ a) $ b))
