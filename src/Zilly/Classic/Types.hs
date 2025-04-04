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
{-# LANGUAGE TypeAbstractions         #-} 

{-# LANGUAGE TemplateHaskell          #-}
-- Template haskell warnings
{-# OPTIONS_GHC -Wno-redundant-constraints #-}


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
module Zilly.Classic.Types (module Zilly.Classic.Types) where


import Prelude.Singletons
    ( (%&&),
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
      TrueSym0)

import Data.Singletons.Decide
import Data.Kind (Constraint, Type)
import Data.Proof
import Control.Applicative (Const(..))
import Debug.Trace (trace)
---------------------------
-- Singletons definitions
---------------------------
import Data.Singletons.TH  
$(singletons [d|
  infixr 0 :->
  data Types 
      = Value Types0
      | Lazy Types 
      | Tuple Types Types 
      | Top 
  
  instance Eq Types where 
    Top == Top = True 
    Tuple a b == Tuple a' b' = (a == a') && (b == b')
    Tuple _ _ == Top = True 
    Top == Tuple _ _ = True
    Tuple _ _ == Value _ = False 
    Tuple _ _ == Lazy _ = False 
    Value _ == Tuple _ _ = False 
    Lazy _ == Tuple _ _ = False
    Value a == Value b = a == b 
    Lazy a == Lazy b = a == b 
    Lazy Top == Top = True 
    Top == Lazy Top = True 
    Lazy a == Value b  = False
    Value a == Lazy b = False 
    Value a == Top = False 
    Top == Value a = False

  data Types0 
    = Z
    | (:->) Types Types
    deriving (Eq)

  lowerBound :: Types -> Types -> Maybe Types
  lowerBound (Tuple a b) (Tuple a' b') = liftA2 Tuple (lowerBound a a') (lowerBound b b')
  lowerBound (Tuple _ _) (Value _) = Nothing 
  lowerBound (Tuple a b) (Lazy a') = lowerBound (Tuple a b) a'
  lowerBound (Value _) (Tuple _ _) = Nothing
  lowerBound (Lazy a') (Tuple a b) = lowerBound a' (Tuple a b)
  lowerBound (Lazy a) (Lazy b) =  Lazy <$> lowerBound a b
  lowerBound (Value (a :-> b)) (Value (c :-> d)) =  Value <$> liftA2 (:->) (upperBound a c ) (lowerBound b d)
  lowerBound (Value a) (Lazy b)  = lowerBound (Value a) b
  lowerBound (Lazy a)  (Value b) = lowerBound a (Value b)
  lowerBound (Value Z) (Value Z) = Just (Value Z)
  lowerBound (Value Z) (Value (_ :-> _)) = Nothing
  lowerBound (Value (_ :-> _)) (Value Z) = Nothing
  lowerBound Top a = Just a 
  lowerBound a Top = Just a



  upperBound :: Types -> Types -> Maybe Types
  upperBound (Tuple a b) (Tuple a' b') = liftA2 Tuple (upperBound a a') (upperBound b b')
  upperBound (Tuple _ _) (Value _) = Nothing 
  upperBound (Tuple a b) (Lazy a') = Lazy  <$> upperBound (Tuple a b) a'
  upperBound (Value _) (Tuple _ _) = Nothing
  upperBound (Lazy a') (Tuple a b) = Lazy <$> upperBound a' (Tuple a b) 
  upperBound (Value (a :-> b)) (Value (c :-> d))  =  Value <$> liftA2 (:->) (lowerBound a c) (upperBound b d)
  upperBound (Lazy a) (Lazy b)   =  Lazy <$> upperBound a b
  upperBound (Value a) (Lazy b)  =  Lazy <$> upperBound (Value a) b
  upperBound (Lazy a)  (Value b) =  Lazy <$> upperBound a (Value b)
  upperBound (Value Z) (Value Z) = Just (Value Z)
  upperBound (Value Z) (Value (_ :-> _)) = Nothing
  upperBound (Value (_ :-> _)) (Value Z) = Nothing
  upperBound Top a = Just Top
  upperBound a Top = Just Top 


  ftype :: Types -> Types 
  ftype (Value Z) = Value Z
  ftype (Value (a :-> b)) = Value (a :-> b)
  ftype (Lazy a) = a
  ftype (Tuple a b) = Tuple (ftype a) (ftype b)
  ftype Top = Top 


  |])

instance Show Types where
  showsPrec p = \case
    (Value a) -> showsPrec p a
    (Lazy a)  -> showString "Lazy <" . showsPrec p a . showString ">"
    Top       -> showString "Var"
    (Tuple a b) -> showString "(" . shows a . showString "," . shows b . showString ")"
instance Show Types0 where
  showsPrec p = \case
    Z -> showString "Z"
    (a :-> b) -> showParen (p > 0) $ showsPrec 1 a . showString " -> " . shows b



instance SDecide Types where 
  STop %~ STop = Proved Refl
  SValue a %~ SValue b = case a %~ b of
    Proved Refl -> Proved Refl 
    Disproved refuted -> Disproved (\Refl -> refuted Refl)
  SLazy a %~ SLazy b = case a %~ b of
    Proved Refl -> Proved Refl 
    Disproved refuted -> Disproved (\Refl -> refuted Refl)
  STuple a b %~ STuple a' b' = case (a %~ a', b %~ b') of 
    (Proved Refl, Proved Refl) -> Proved Refl 
    (Disproved refuted, _) -> Disproved $ \Refl -> refuted Refl
    (_,Disproved refuted) -> Disproved $ \Refl -> refuted Refl
  _ %~ _ = Disproved $ \_ -> error "Trying to eval Void"


---------------------------
-- Type synonyms
---------------------------

type Symbol = String
type VZ     = Value Z

infixr 0 ~>
type (~>) a b = Value (a :-> b)

infixr 0 ~~>

(~~>) :: Types -> Types -> Types
a ~~> b = Value $ a :-> b


--------------------------
-- Utility functions
--------------------------


-- | Implicit equality.
decideEquality' :: forall {k} (a :: k) (b :: k).  (SDecide k, SingI a, SingI b) => Maybe (a :~: b) 
decideEquality' = decideEquality (sing @a) (sing @b)

--------------------------
-- Dictionary Injection
--------------------------

-- | Show implicit singleton.
withShow :: forall (z :: Types). SingI z => String
withShow = show $ fromSing (sing @z) 

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
withSingILBType f = case sLowerBound (sing @z0) (sing @z1) of
  SJust ub -> withSingI ub f
  SNothing -> f
 
withSingIFtype :: forall a r. SingI a => (SingI (Ftype a) => r) -> r
withSingIFtype f = case sing @a of 
  SValue SZ            -> f
  SValue ((:%->) _ _ ) -> f
  SLazy  sa         -> withSingI sa $ f
  STuple @sa @sb sa sb      -> withSingI sa $ withSingI sb $ withSingIFtype @sa $ withSingIFtype @sb $ f 
  STop                 -> f

withSingIEq :: forall {k} (a :: k) (b :: k) r. (SingI a, SingI b, SEq k) => (SingI (a == b) => r) -> r
withSingIEq f = withSingI (sing @a %== sing @b) $ f

eqIsReflexive :: forall {k} (a :: k) r. (SingI a, SEq k) => (((a == a) ~ True) => r) -> r
eqIsReflexive f = case sing @a %== sing @a of 
  STrue -> f
  SFalse -> error "impossible case"

eqIsCommutative :: forall {k} (a :: k) (b :: k) r.
  ( SingI a
  , SingI b
  , SEq k
  ) => (((a==b) ~ (b==a)) => r) -> r
eqIsCommutative f 
  = withSingIEq @a @b 
  $ withSingIEq @b @a 
  $ case decideEquality (sing @(a==b)) (sing @(b==a)) of
    Nothing -> error "impossible case"
    Just Refl -> f

eqIsTransitive :: forall {k} (a :: k) (b :: k) (c :: k) r. 
  ( SingI a
  , SingI b
  , SingI c
  , SEq k
  , (a == b) ~ True 
  , (b == c) ~ True
  ) => (((a == c) ~ True) => r) -> r
eqIsTransitive f 
  = withSingIEq @a @b 
  $ withSingIEq @b @c
  $ withSingIEq @a @c 
  $ case decideEquality (sing @(a==c)) STrue of 
    Nothing -> error "impossible case"
    Just Refl -> f

eqWeakening :: forall {k} (a :: k) (b :: k) r.
  ( SingI a
  , SingI b
  , SDecide k
  , SEq k
  , a ~ b
  ) => (( (a == b) ~ True ) => r) -> r
eqWeakening f = eqIsReflexive @a $ f

eqLeibniz :: forall {k} (a :: k) (b :: k) (c :: k) r.
  ( SingI a
  -- , SingI b
  , SDecide k
  , SEq k 
  , a ~ c
  ) => (( (a == b) ~ (c == b)  ) => r) -> r
eqLeibniz f = eqIsReflexive @a $ f


-------------------------
-- Properties
--------------------------

{-| Upperbound being a meet, is axiomatically commutative. 

\[a \vee b = b \vee a\]
-}
ubIsCommutative :: forall (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  )
  => ( ((UpperBound a b == UpperBound b a) ~ True) => cont) -> cont
ubIsCommutative f 
  = withSingIUBType @a @b
  $ withSingIUBType @b @a 
  $ withSingIEq @(UpperBound a b) @(UpperBound b a)
  $ case decideEquality (sing @(UpperBound a b == UpperBound b a)) STrue of 
    Just Refl -> f
    Nothing -> error "impossible case"

ubIsCommutative' :: forall (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  )
  => ( (UpperBound a b ~ UpperBound b a) => cont) -> cont
ubIsCommutative' f 
  = withSingIUBType @a @b
  $ withSingIUBType @b @a 
  $ case decideEquality (sing @(UpperBound a b)) (sing @(UpperBound b a)) of 
    Just Refl -> f
    Nothing -> error "impossible case"





lbIsCommutative :: forall (a :: Types) (b :: Types) cont.
  ( SingI a
  , SingI b
  )
  => (((LowerBound a b == LowerBound b a) ~ True) => cont) -> cont
lbIsCommutative f 
  = withSingILBType @a @b 
  $ withSingILBType @b @a 
  $ withSingIEq @(LowerBound a b) @(LowerBound b a)
  $ case decideEquality (sing @(LowerBound a b == LowerBound b a)) STrue of 
    Just Refl -> f
    Nothing -> error "impossible case"

ftypeIsSubtype :: forall a r. SingI a => (((UpperBound a (Ftype a) == Just a) ~ True) => r) -> r
ftypeIsSubtype f = withSingIFtype @a $ case sing @a of 
  SValue SZ -> f 
  SValue ((:%->) @sa @sb sa sb) 
    -> withSingI sa 
    $ withSingI sb  
    $ lbIsIdempotent @sa 
    $ ubIsIdempotent @sb 
    $ eqIsReflexive @sa 
    $ eqIsReflexive @sb
    $ f 
  SLazy (SValue SZ) -> f
  SLazy (SValue ((:%->) @sa @sb sa sb) )
    -> withSingI sa 
    $ withSingI sb  
    $ lbIsIdempotent @sa 
    $ ubIsIdempotent @sb 
    $ eqIsReflexive @sa 
    $ eqIsReflexive @sb
    $ f
  SLazy @slsa (SLazy @sa sa)  
    -> withSingIFtype @a
    $  withSingIUBType @a @(Ftype a)
    $  withSingIEq @(UpperBound a (Ftype a)) @(Just a)
    $ case decideEquality (sing @(UpperBound a (Ftype a) == Just a)) STrue of 
      Just Refl -> f 
      Nothing -> error "impossible case"
  SLazy STop ->  f
  SLazy @st st@(STuple {}) -> eqIsReflexive @st $ ubIsIdempotent @st $ f
  STuple @sa @sb sa sb 
    -> withSingI sa 
    $  withSingI sb 
    $  ftypeIsSubtype @sa 
    $  ftypeIsSubtype @sb 
    $  case (sUpperBound sa $ sFtype sa, sUpperBound sb $ sFtype sb) of
      (SJust _, SJust _) -> f
      
  STop -> f

ftypeRespectsUpperBound :: forall {x} a b r. 
  ( SingI a 
  , SingI b 
  , UpperBound a b ~ Just x
  ) 
  => (((UpperBound (Ftype a) (Ftype b)) ~ Just (Ftype x) ) => r) -> r
ftypeRespectsUpperBound f 
  = withSingIFtype @a 
  $ withSingIFtype @b 
  $ withSingIUBType @a @b 
  $ withSingIUBType @(Ftype a) @(Ftype b)
  $ case sing @(UpperBound a b) of
    SJust @_ @sx sx 
      -> withSingI sx 
      $  withSingIFtype @sx
      $ case decideEquality (sing @(UpperBound (Ftype a) (Ftype b)) ) (sing @(Just (Ftype sx))) of
        Nothing -> error "impossible case"
        Just Refl -> f

ftypeRespectsEquality :: forall a b r. 
  ( SingI a
  , SingI b
  , (a == b) ~ True 
  ) => ((Ftype a == Ftype b) ~ True => r) -> r
ftypeRespectsEquality f 
  = withSingIFtype @a 
  $ withSingIFtype @b
  $ withSingIEq @a @b
  $ withSingIEq @(Ftype a) @(Ftype b)
  $ case decideEquality (sing @(Ftype a == Ftype b)) STrue of 
    Just Refl -> f
    Nothing   -> error "impossible case"

{-| Upperbound being a meet, is axiomatically associative. 

\[a \vee b = b \vee a\]
-}
-- ubIsAssociative :: forall {r1 :: Maybe Types} {r2 :: Maybe Types} (a :: Types) (b :: Types) (c :: Types) cont.
--   ( SingI a 
--   , SingI b
--   , SingI c
--   , (UpperBound a b >>= UpperBoundSym1 c) ~ r1
--   , (UpperBound b c >>= UpperBoundSym1 a) ~ r2
--   ) => (r1 ~ r2 => cont) -> Maybe cont
-- ubIsAssociative f
--   = withSingIUBType @a @b 
--   $ withSingIUBType @b @c
--   $ case (sing @(UpperBound a b), sing @(UpperBound b c)) of
--   (SJust @_ @x x,SJust @_ @y y) 
--     -> withSingI x
--     $ withSingI y 
--     $ withSingIUBType @c @x 
--     $ withSingIUBType @a @y 
--     $ case decideEquality' @(Maybe Types) @(UpperBound c x) @(UpperBound a y) of
--       Just Refl -> Just f
--       Nothing -> Nothing
--   _ -> Nothing
--
ubIsAssociative :: forall {r1 :: Maybe Types} {r2 :: Maybe Types} (a :: Types) (b :: Types) (c :: Types) cont.
  ( SingI a 
  , SingI b
  , SingI c
  , (UpperBound a b >>= UpperBoundSym1 c) ~ r1
  , (UpperBound b c >>= UpperBoundSym1 a) ~ r2
  ) => (r1 ~ r2 => cont) -> cont
ubIsAssociative f = case (sing @a, sing @b, sing @c) of 
  (SValue SZ, SValue SZ, SValue SZ) -> f
  _ -> undefined

lbIsAssociative :: forall {r1 :: Maybe Types} {r2 :: Maybe Types} (a :: Types) (b :: Types) (c :: Types) cont.
  ( SingI a 
  , SingI b
  , SingI c
  , (LowerBound a b >>= LowerBoundSym1 c) ~ r1
  , (LowerBound b c >>= LowerBoundSym1 a) ~ r2
  ) => (r1 ~ r2 => cont) -> cont
lbIsAssociative _ = error "not defined" 

{-| Upperbound being a meet, is axiomatically reflexive. 

\[a \vee a = a\]
-}
ubIsIdempotent :: forall (a :: Types) cont.
  (SingI a)
  => (UpperBound a a ~ Just a => cont) -> cont
ubIsIdempotent f = case sing @a of 
  (SValue SZ) -> case sUpperBound (SValue SZ) (SValue SZ) of 
    SJust _ -> f
  (SValue ((:%->) @sa @sb sa sb)) 
    -> withSingI sa 
    $  withSingI sb 
    $ ubIsIdempotent @sb 
    $ lbIsIdempotent @sa 
    $ case (sLowerBound sa sa, sUpperBound sb sb) of 
      (SJust _, SJust _ ) -> f  
  (SLazy @sa sa) 
    -> withSingI sa 
    $ ubIsIdempotent @sa 
    $ f 
  (STuple @sa @sb sa sb) 
    -> withSingI sa
    $ withSingI sb 
    $ ubIsIdempotent @sa
    $ ubIsIdempotent @sb 
    $ f
  STop -> f
  
lbIsIdempotent :: forall (a :: Types) cont.
  (SingI a)
  => (LowerBound a a ~ Just a => cont) -> cont
lbIsIdempotent f = case sing @a of 
  (SValue SZ) -> case sLowerBound (SValue SZ) (SValue SZ) of 
    SJust _ -> f
  (SValue ((:%->) @sa @sb sa sb)) 
    -> withSingI sa 
    $  withSingI sb 
    $ ubIsIdempotent @sa 
    $ lbIsIdempotent @sb  
    $ case (sUpperBound sa sa, sLowerBound sb sb) of 
      (SJust _, SJust _ ) -> f  
  (SLazy @sa sa) 
    -> withSingI sa 
    $ lbIsIdempotent @sa 
    $ f 
  (STuple @sa @sb sa sb) 
    -> withSingI sa
    $ withSingI sb 
    $ lbIsIdempotent @sa
    $ lbIsIdempotent @sb 
    $ f
  STop -> f
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
ubIsTransitive _ = error "not implemented"

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
ubIsTransitive' !f 
  = withSingIUBType @a @c 
  $ case decideEquality (sing @(UpperBound a c)) (sing @(Just r0)) of
    Just Refl -> f
    Nothing -> error "impossible case"

ubIsInjective
  :: forall {r0 :: Types} (f :: Types -> Types) (a :: Types) (b :: Types) cont. 
  ( UpperBound (f a) (f b) ~ Just (f r0)
  , SingI a 
  , SingI b
  , SingI r0
  ) => (UpperBound a b ~ Just r0 => cont) -> cont
ubIsInjective f 
  =  withSingIUBType @a @b 
  $ case decideEquality (sing @(UpperBound a b)) (sing @(Just r0)) of
    Just Refl -> f 
    Nothing   -> error "impossible case"


ubIsInjective'
  :: forall  (f :: Types -> Types) (a :: Types) (b :: Types) cont. 
  ( UpperBound (f a) (f b) ~ Nothing 
  , SingI a 
  , SingI b
  ) => (UpperBound a b ~ Nothing => cont) -> cont
ubIsInjective' f 
  =  withSingIUBType @a @b 
  $ case decideEquality (sing @(UpperBound a b)) (sing @Nothing) of
    Just Refl -> f 
    Nothing   -> error "impossible case"


ubPreservesFunctionForm :: forall arg body y c cont. 
  ( (UpperBound (Value (arg :-> body)) y == Just c) ~ True
  , SingI y
  ) => (forall arg' body'. (y ~ (Value (arg' :-> body')), SingI arg', SingI body') => cont) -> cont 
ubPreservesFunctionForm f = case sing @y of 
  SValue ((:%->) @a @b a b) -> withSingI a $ withSingI b $ f @a @b
  _ -> error "impossible case"

ubPreservesFunctionForm' :: forall x y c arg body cont. 
  ( x ~ Value (arg :-> body)
  , (UpperBound x y == Just c ) ~ True
  , SingI y
  , SingI x
  ) => (forall arg' body'. (y ~ (Value (arg' :-> body')), SingI arg', SingI body') => cont) -> cont 
ubPreservesFunctionForm' f 
  = case sing @x of
    SValue ((:%->) arg body)
      -> withSingI arg 
      $ withSingI body 
      $ withSingIUBType @x @y
      $ withSingIUBType @(Value (arg :-> body)) @y
      $ eqLeibniz @(UpperBound x y) @(Just c) @(UpperBound (Value (arg :-> body)) y)
      $ ubPreservesFunctionForm @arg @body @y @c $ f


{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = c\]
\[a \vee c = c\]
-}
ubIsUb :: forall (a :: Types) (b :: Types) r0 cont.
  ( UpperBound a b ~ Just r0 
  , SingI a
  , SingI b
  , SingI r0
  ) 
  => (UpperBound a r0 ~ Just r0 => cont) -> cont
ubIsUb !f =  withSingIUBType @a @r0 $  case decideEquality (sing @(UpperBound a r0 )) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"

type TypesCaseAnalysis (c :: Types -> Constraint) = 
    ( C c Value
    , C c Lazy 
    , c Top
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
  STop     -> Dict

---------------------
-- Upcasting
---------------------

data UpperBoundResults f a b where
  NonExistentUB   :: (UpperBound a b ~ Nothing) => UpperBoundResults f a b 
  SameTypeUB      :: (a ~ b, UpperBound a b ~ Just a, UpperBound a b ~ Just b) => f a -> UpperBoundResults f a b 
  LeftUB          :: (UpperBound a b ~ Just a)  => f a -> UpperBoundResults f a b 
  RightUB         :: (UpperBound a b ~ Just b)  => f b -> UpperBoundResults f a b 
  SomethingElseUB :: forall (r :: Types) f (a :: Types) (b :: Types) . 
    ( UpperBound a b ~ Just r
    , SingI r
    ) => f r -> UpperBoundResults f a b 

data LowerBoundResults f a b where
  NonExistentLB   :: (LowerBound a b ~ Nothing) => LowerBoundResults f a b 
  SameTypeLB      :: (a ~ b, LowerBound a b ~ Just a, LowerBound a b ~ Just b) => f a -> LowerBoundResults f a b 
  LeftLB          :: (LowerBound a b ~ Just a)  => f a -> LowerBoundResults f a b 
  RightLB         :: (LowerBound a b ~ Just b)  => f b -> LowerBoundResults f a b 
  SomethingElseLB :: forall (r :: Types) f (a :: Types) (b :: Types) . 
    ( LowerBound a b ~ Just r
    , SingI r
    ) => f r -> LowerBoundResults f a b 



pattern SameTypeUBN ::  (a ~ b, UpperBound a b ~ Just a) => UpperBoundResults (Const ()) a b 
pattern SameTypeUBN <- SameTypeUB (Const ())
  where SameTypeUBN =  SameTypeUB (Const ())
  

pattern LeftUBN ::  (UpperBound a b ~ Just a) => UpperBoundResults (Const ()) a b 
pattern LeftUBN <- LeftUB (Const ())
  where LeftUBN = LeftUB (Const ())

pattern RightUBN ::  (UpperBound a b ~ Just b) => UpperBoundResults (Const ()) a b 
pattern RightUBN <- RightUB (Const ())
  where RightUBN = RightUB (Const ())

pattern SomethingElseUBN :: 
  ( UpperBound a b ~ Just r
  , SingI r
  ) => UpperBoundResults (Const ()) a b 
pattern SomethingElseUBN <- SomethingElseUB (Const ())
  where SomethingElseUBN = SomethingElseUB (Const ())

upcastable 
  :: forall 
    (a :: Types) 
    (b :: Types).
  ( SingI a
  , SingI b
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
            -> withSingI sub 
            $  SomethingElseUBN @a @b
      SNothing  -> NonExistentUB

downcastable 
  :: forall 
    (a :: Types) 
    (b :: Types).
  ( SingI a
  , SingI b
  ) => LowerBoundResults (Const ()) a b
downcastable 
  = withSingILBType @a @b 
  $ case decideEquality (sing @a) (sing @b) of
    Just Refl -> lbIsIdempotent @a $ SameTypeLB (Const ())
    Nothing -> case sing @(LowerBound a b) of
      SJust sub -> case decideEquality (sing @a) sub of
        Just Refl -> LeftLB (Const ())
        Nothing   -> case decideEquality (sing @b) sub of
          Just Refl -> RightLB (Const ())
          Nothing   
            -> withSingI sub 
            $  SomethingElseLB @_ @_ @a @b (Const ())
      SNothing  -> NonExistentLB


