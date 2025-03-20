
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
-- {-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE TemplateHaskell          #-}


{-|
Module      : Zilly.Types
Description : Definition of types, properties and evidence injection for Zilly.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Defines the types of the Zilly language, provides some type level properties
and a way to inject them via continnuations.
-}
module Zilly.Types where


import Prelude.Singletons
    ( withSingI,
      SingI(..),
      SingKind(fromSing),
      (%&&),
      (%<$>),
      LiftA2Sym0,
      PMonad(type (>>=)),
      SApplicative(sLiftA2),
      type (&&@#@$),
      type (==@#@$),
      PEq(type (==)),
      SEq((%==)),
      type (<$>@#@$),
      FalseSym0,
      JustSym0,
      NothingSym0,
      SBool(SFalse, STrue),
      SMaybe(SJust, SNothing),
      TrueSym0 )
import Data.Singletons.Decide
import Control.Applicative (Const(..))
import Data.Kind (Type,Constraint)
import Data.Proof



---------------------------
-- Singletons definitions
---------------------------
import Data.Singletons.TH  hiding (Const)
$(singletons [d|
  infixr 0 :->
  data Types 
      = Value Types0
      | Lazy Types 
      | LazyS Types
      | Array Types
      | Tuple Types Types
    deriving (Eq)

  data Types0 
    = Z
    | F
    | (:->) Types Types
    deriving (Eq)

  lowerBound :: Types -> Types -> Maybe Types
  lowerBound (Array a) (Array b) = Array <$> lowerBound a b
  lowerBound (Lazy a) (Lazy b) =  Lazy <$> lowerBound a b
  lowerBound (Value (a :-> b)) (Value (c :-> d)) =  Value <$> liftA2 (:->) (upperBound a c ) (lowerBound b d)
  lowerBound (Value a) (Lazy b)  = lowerBound (Value a) b
  lowerBound (Lazy a)  (Value b) = lowerBound a (Value b)
  lowerBound (Value Z) (Value Z) = Just (Value Z)
  lowerBound (Value Z) (Value F) = Just (Value Z)
  lowerBound (Value F) (Value Z) = Just (Value Z)
  lowerBound (Value F) (Value F) = Just (Value F)
  lowerBound (Value Z) (Value (_ :-> _)) = Nothing
  lowerBound (Value (_ :-> _)) (Value Z) = Nothing
  lowerBound (Array _) (Value _)  = Nothing
  lowerBound (Value _) (Array _)  = Nothing
  lowerBound (Array _) (Lazy _)   = Nothing
  lowerBound (Lazy _) (Array _)   = Nothing
  lowerBound (Array _) (LazyS _)  = Nothing
  lowerBound (LazyS _) (Array _)  = Nothing



  upperBound :: Types -> Types -> Maybe Types
  upperBound (Array a) (Array b) = Array <$> upperBound a b
  upperBound (Value (a :-> b)) (Value (c :-> d))  =  Value <$> liftA2 (:->) (lowerBound a c) (upperBound b d)
  upperBound (Lazy a) (Lazy b)   =  Lazy <$> upperBound a b
  upperBound (Value a) (Lazy b)  =  Lazy <$> upperBound (Value a) b
  upperBound (Lazy a)  (Value b) =  Lazy <$> upperBound a (Value b)
  upperBound (Value Z) (Value Z) = Just (Value Z)
  upperBound (Value Z) (Value F) = Just (Value F)
  upperBound (Value F) (Value Z) = Just (Value F)
  upperBound (Value F) (Value F) = Just (Value F)
  upperBound (Value Z) (Value (_ :-> _)) = Nothing
  upperBound (Value (_ :-> _)) (Value Z) = Nothing
  upperBound (Array _) (Value _)  = Nothing
  upperBound (Value _) (Array _)  = Nothing
  upperBound (Array _) (Lazy _)   = Nothing
  upperBound (Lazy _) (Array _)   = Nothing
  upperBound (Array _) (LazyS _)  = Nothing
  upperBound (LazyS _) (Array _)  = Nothing


  baseType :: Types -> Types
  baseType (Array a)          = Array a
  baseType (Value Z)          = Value Z
  baseType (Value (a :-> b))  = Value (a :-> b)
  baseType (Lazy (Value a))   = Value a
  baseType (Lazy (Lazy a))    = baseType a
  baseType (Lazy (LazyS a))   = baseType a
  baseType (LazyS (Value a))  = Value a
  baseType (LazyS (Lazy a))   = baseType a
  baseType (LazyS (LazyS a))  = baseType a

  |])

instance Show Types where
  showsPrec p = \case
    (Value a) -> showsPrec p a
    (Lazy a)  -> showString "Lazy <" . showsPrec p a . showString ">"
    (LazyS a) -> showString "Lazy* <" . showsPrec p a . showString ">"
    (Array a) -> showString "array[" . showsPrec p a . showString "]"
instance Show Types0 where
  showsPrec p = \case
    Z -> showString "Z"
    (a :-> b) -> showParen (p > 0) $ showsPrec 1 a . showString " -> " . shows b

---------------------------
-- Type synonyms
---------------------------

type Symbol = String

infixr 0 ~>
type (~>) a b = Value (a :-> b)

infixr 0 ~~>

(~~>) :: Types -> Types -> Types
a ~~> b = Value $ a :-> b


class SingI a => BasicType a where
  type HashType a :: Type


--------------------------
-- Utility functions
--------------------------


-- | Implicit equality.
decideEquality' :: forall k (a :: k) (b :: k).  (SDecide k, SingI a, SingI b) => Maybe (a :~: b) 
decideEquality' = decideEquality (sing @a) (sing @b)

--------------------------
-- Dictionary Injection
--------------------------

-- | Show implicit singleton.
withShow :: forall (z :: Types). SingI z => String
withShow = show $ fromSing (sing @z) 

{- -- | Injects base type singleton.
withBType :: forall (z :: Types) r. SingI z => (SingI  (BaseType z) => r) -> r
withBType f = case sing @z of
  (SValue @n SZ) -> case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SValue @n (a :%-> b)) -> case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) 
    -> withSingI sa 
    $ withBType @n 
    $ case decideEquality  (sing @(BaseType z)) (sing @(BaseType n) )of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) 
    -> withSingI @n sa 
    $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented" -}

-- | Injects an upper bound singleton.
withSingIUBType :: forall (z0 :: Types) (z1 :: Types) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (UpperBound z0 z1) => r) -> r
withSingIUBType f = case sUpperBound (sing @z0) (sing @z1) of
  SJust ub -> withSingI ub f
  SNothing -> f

-- | Injects a lower bound singleton.
withSingILBType :: forall (z0 :: Types) (z1 :: Types) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (LowerBound z0 z1) => r) -> r
withSingILBType f = undefined 


{- withBVType' :: forall (z :: Types) r. Sing z -> (SingI  (BaseType z) => r) -> r
withBVType' z f= case z of
  (SValue @n _) -> withSingI z $ case decideEquality' @_ @(Value n) @(BaseType z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ withBType @n $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl ->  f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(BaseType z) @(BaseType n) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented" -}



--------------------------
-- Properties
--------------------------

{-| Upperbound being a meet, is axiomatically commutative. 

\[a \vee b = b \vee a\]
-}
ubIsCommutative :: forall (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  )
  => ((UpperBound a b ~ UpperBound b a) => cont) -> cont
ubIsCommutative f 
  = withSingIUBType @a @b 
  $ withSingIUBType @b @a 
  $ case decideEquality (sing @(UpperBound a b)) (sing @(UpperBound b a)) of
  Just Refl -> f
  Nothing -> error "impossible case"


{-| Upperbound being a meet, is axiomatically associative. 

\[a \vee b = b \vee a\]
-}
ubIsAssociative :: forall {r1 :: Maybe Types} {r2 :: Maybe Types} (a :: Types) (b :: Types) (c :: Types) cont.
  ( SingI a 
  , SingI b
  , SingI c
  , (UpperBound a b >>= UpperBoundSym1 c) ~ r1
  , (UpperBound b c >>= UpperBoundSym1 a) ~ r2
  ) => (r1 ~ r2 => cont) -> Maybe cont
ubIsAssociative f
  = withSingIUBType @a @b 
  $ withSingIUBType @b @c
  $ case (sing @(UpperBound a b), sing @(UpperBound b c)) of
  (SJust @_ @x x,SJust @_ @y y) 
    -> withSingI x
    $ withSingI y 
    $ withSingIUBType @c @x 
    $ withSingIUBType @a @y 
    $ case decideEquality' @(Maybe Types) @(UpperBound c x) @(UpperBound a y) of
      Just Refl -> Just f
      Nothing -> Nothing
  _ -> Nothing



{-| Upperbound being a meet, is axiomatically reflexive. 

\[a \vee a = a\]
-}
ubIsIdempotent :: forall (a :: Types) cont.
  (SingI a)
  => (UpperBound a a ~ Just a => cont) -> cont
ubIsIdempotent !f = withSingIUBType @a @a $ case decideEquality (sing @(UpperBound a a)) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"

-- ask reddit: why I can't apply type families and ~ inside a contraint-kind?
{- type UBAxioms = 
  ( forall a b. (UpperBound a b ~ UpperBound b a)
  , forall a. UpperBound a a ~ Just a
  , forall a b c. (UpperBound a b >>= UpperBoundSym1 c) ~ (UpperBound b c >>= UpperBoundSym1 a)
  ) -}


ubIsTransitive 
  :: forall {r0 :: Types} {r1 :: Types} {r2 :: Types} a b c cont.
  ( UpperBound a b ~ Just r0
  , UpperBound b c ~ Just r1 
  )
  => (UpperBound a c ~ Just r2 => cont) -> cont
ubIsTransitive fa = error "not implemented"

{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = b\]
-}
ubIsTransitive'
  :: forall {r0 :: Types} a b c cont.
  ( UpperBound a b ~ Just b
  , UpperBound b c ~ Just r0
  , SingI r0
  , SingI a
  , SingI c
  )
  => (UpperBound a c ~ Just r0 => cont) -> cont
ubIsTransitive' !f = withSingIUBType @a @c $ case decideEquality (sing @(UpperBound a c)) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"

ubIsInjective
  :: forall {r0 :: Types} (f :: Types -> Types) (a :: Types) (b :: Types) cont. 
  ( UpperBound (f a) (f b) ~ Just (f r0)
  , SingI a 
  , SingI b
  , SingI r0
  ) => (UpperBound a b ~ Just r0 => cont) -> cont
ubIsInjective f =  withSingIUBType @a @b $ case decideEquality (sing @(UpperBound a b)) (sing @(Just r0)) of
  Just Refl -> f 
  Nothing   -> error "impossible case"


ubIsInjective'
  :: forall  (f :: Types -> Types) (a :: Types) (b :: Types) cont. 
  ( UpperBound (f a) (f b) ~ Nothing 
  , SingI a 
  , SingI b
  ) => (UpperBound a b ~ Nothing => cont) -> cont
ubIsInjective' f =  withSingIUBType @a @b $ case decideEquality (sing @(UpperBound a b)) (sing @Nothing) of
  Just Refl -> f 
  Nothing   -> error "impossible case"





{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = c\]
\[a \vee c = c\]
-}
ubIsUb :: forall {r0 :: Types} (a :: Types) (b :: Types) cont.
  ( UpperBound a b ~ Just r0 
  , SingI a
  , SingI b
  , SingI r0
  ) 
  => (UpperBound a r0 ~ Just r0 => cont) -> cont
ubIsUb !f =  withSingIUBType @a @r0 $  case decideEquality (sing @(UpperBound a r0 )) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"


btIsInductive :: forall {b} (a :: Types) cont.
  ( SingI a
  , BaseType a ~ b
  ) => (BaseType (Lazy a) ~ b => cont) -> cont
btIsInductive f = undefined


type family HasLazy (x :: Types) :: Bool where 
  HasLazy (Value _) = False 
  HasLazy (Array a) = HasLazy a
  HasLazy (LazyS a) = HasLazy a
  HasLazy (Lazy _)  = True


type TypesCaseAnalysis (c :: Types -> Constraint) = 
    ( C c Value
    , C c Lazy 
    , C c LazyS
    , C c Array 
    )

typesCaseAnalysis :: forall 
  (c :: Types -> Constraint)
  (x :: Types).
  ( TypesCaseAnalysis c
  , SingI x 
  ) => Dict (c x) 
typesCaseAnalysis = case sing @x of 
  SValue _ -> Dict 
  SLazy  _ -> Dict 
  SLazyS _ -> Dict 
  SArray _ -> Dict


