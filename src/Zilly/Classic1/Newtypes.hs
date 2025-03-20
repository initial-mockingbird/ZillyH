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
{-# Language PatternSynonyms          #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell          #-}
-- Template haskell warnings
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Zilly.Classic1.Newtypes where 

import Data.Singletons.TH (singletons,genSingletons, promote)
import Prelude.Singletons hiding (Const)
    -- ( (%&&),
    --   (%<$>),
    --   LiftA2Sym0,
    --   PMonad(type (>>=)),
    --   SApplicative(sLiftA2),
    --   type (&&@#@$),
    --   type (==@#@$),
    --   PEq(type (==)),
    --   SEq((%==)),
    --   type (<$>@#@$),
    --   FalseSym0,
    --   JustSym0,
    --   NothingSym0,
    --   SBool(SFalse, STrue),
    --   SMaybe(SJust, SNothing),
    --   TrueSym0)

import Data.Singletons.Decide
import Data.Kind (Constraint, Type)
import Data.Proof
import Control.Applicative (Const(..))
import Debug.Trace (trace)
import Data.String 
import Data.String.Singletons
import Data.List.Singletons
import GHC.TypeLits.Singletons
import GHC.TypeLits
import Data.Singletons.TH.Options
import Language.Haskell.TH qualified as TH 
import Data.Text (Text)
import Data.Text qualified as Text
import Unsafe.Coerce

type Name  = Text
type PName = Symbol 


newtype TVar  = TV Name deriving (Eq)
newtype PTVar = PTV PName deriving (Eq)

data Types 
  = TCon Name [Types]
  | TVar TVar 

data PTypes 
  = PTCon PName  [PTypes]
  | PTVar PTVar 

-- ftype :: Types -> Types 
-- ftype (TCon "Lazy" [a])    = a
-- ftype (TCon "Tuple" [a,b]) = TCon "Tuple" [ftype a, ftype b]
-- ftype (TCon "ZArray" [a])  = TCon "ZArray" [ftype a]
-- ftype a                    = a
--
-- type family Ftype (a :: PTypes) :: PTypes where 
--   Ftype (PTCon "Lazy" '[a])    = a
--   Ftype (PTCon "Tuple" [a,b]) = PTCon "Tuple" [Ftype a, Ftype b]
--   Ftype (PTCon "ZArray" '[a])  = PTCon "ZArray" '[Ftype a]
--   Ftype a                    = a
--  


$(let customPromote :: TH.Name -> TH.Name 
      customPromote n 
        | n == ''TVar   = ''PTVar 
        | n == 'TV      = 'PTV 
        | n == ''Types  = ''PTypes
        | n == 'TCon    = 'PTCon 
        | n == 'TVar    = 'PTVar
        | n == ''Text   = ''Symbol
        | n == ''Name   = ''Symbol
        | otherwise = promotedDataTypeOrConName defaultOptions n

      customDefun :: TH.Name -> Int -> TH.Name 
      customDefun n sat = defunctionalizedName defaultOptions (customPromote n) sat in
  withOptions defaultOptions{ promotedDataTypeOrConName = customPromote
                            , defunctionalizedName      = customDefun
                            } $ do
    ds0 <- genSingletons [''TVar, ''Types] 
    ds1 <- singletons [d|
      instance Eq Types where 
        TCon x as == TCon y bs = (x == y) && (as == bs)
      |]
    ds2 <- promote [d|
      ftype :: Types -> Types 
      ftype (TCon "Lazy" [a])    = a
      ftype (TCon "Tuple" [a,b]) = TCon "Tuple" [ftype a, ftype b]
      ftype (TCon "Array" [a])  = TCon "Array" [ftype a]
      ftype a                    = a     

      monoConstructor :: Text -> Types -> Types 
      monoConstructor s x = TCon s [x]

      biConstructor :: Text -> Types -> Types -> Types 
      biConstructor s x y = TCon s [x,y]
      
      upperBound :: Types -> Types -> Maybe Types 
      upperBound (TCon "Array" [a]) (TCon "Array" [b]) = monoConstructor "Array" <$> upperBound a b
      upperBound (TCon "->" [a0,b0]) (TCon "->" [a1,b1]) 
        = liftA2 (biConstructor "->") (lowerBound a0 a1) (upperBound b0 b1)
      upperBound (TCon "Tuple" [a0,b0]) (TCon "Tuple" [a1,b1]) 
        = liftA2 (biConstructor "Tuple") (upperBound a0 a1) (upperBound b0 b1)
      upperBound (TCon "Lazy" [a]) (TCon "Lazy" [b]) = monoConstructor "Lazy" <$> upperBound a b  
      upperBound (TCon "Z" []) (TCon "F" []) = Just (TCon "F" [])
      upperBound (TCon "F" []) (TCon "Z" []) = Just (TCon "F" [])
      upperBound (TCon "Lazy" [a]) b = monoConstructor "Lazy" <$> upperBound a b 
      upperBound b (TCon "Lazy" [a]) = monoConstructor "Lazy" <$> upperBound b a 
      upperBound a b = if a == b then Just a else Nothing


      lowerBound :: Types -> Types -> Maybe Types 
      lowerBound (TCon "Z" []) (TCon "Z" []) = Just (TCon "Z" [])
      lowerBound (TCon "Array" [a]) (TCon "Array" [b]) = monoConstructor "Array" <$> lowerBound a b
      lowerBound (TCon "->" [a0,b0]) (TCon "->" [a1,b1]) 
        = liftA2 (biConstructor "->") (upperBound a0 a1) (lowerBound b0 b1)
      lowerBound (TCon "Tuple" [a0,b0]) (TCon "Tuple" [a1,b1]) 
        = liftA2 (biConstructor "Tuple") (lowerBound a0 a1) (lowerBound b0 b1)
      lowerBound (TCon "Lazy" [a]) (TCon "Lazy" [b]) = monoConstructor "Lazy" <$> lowerBound a b  
      lowerBound (TCon "Z" []) (TCon "F" []) = Just (TCon "Z" [])
      lowerBound (TCon "F" []) (TCon "Z" []) = Just (TCon "Z" [])
      lowerBound (TCon "Lazy" [a]) b = monoConstructor "Lazy" <$> lowerBound a b 
      lowerBound b (TCon "Lazy" [a]) = monoConstructor "Lazy" <$> lowerBound b a 
      lowerBound a b = if a == b then Just a else Nothing


      |]
    pure $ ds0 <> ds1 <> ds2 


  
  )

infixr 0 :->
pattern Z         = TCon "Z"      []
pattern a :-> b   = TCon "->"     [a, b]
pattern Lazy a    = TCon "Lazy"   [a]
pattern Tuple a b = TCon "Tuple"  [a,b]
pattern Top       = TCon "Top"    []
pattern Bot       = TCon "Bot"    []
pattern F         = TCon "F"      []
pattern ZString   = TCon "String" []
pattern ZBool     = TCon "Bool"   []
pattern ZNull     = TCon "Null"   []
pattern ZDouble   = TCon "F" []
pattern ZInfer    = TCon "Infer"  []
pattern LazyS a   = TCon "Lazy*"  [a]
pattern ZArray a  = TCon "Array" [a]

infixr 0 -->
type PZ         = PTCon "Z"      '[]
type a --> b    = PTCon "->"     '[a, b]
type PLazy a    = PTCon "Lazy"   '[a]
type PTuple a b = PTCon "Tuple"  '[a,b]
type PTop       = PTCon "Top"    '[]
type PBot       = PTCon "Bot"    '[]
type PF         = PTCon "F"      '[]
type PZString   = PTCon "String" '[]
type PZBool     = PTCon "Bool"   '[]
type PZNull     = PTCon "Null"   '[]
type PZDouble   = PTCon "F" '[]
type PZInfer    = PTCon "Infer"  '[]
type PLazyS a   = PTCon "Lazy*"  '[a]
type PZArray a  = PTCon "Array" '[a]

matches :: forall (a :: Symbol) (b :: Symbol). SingI a => SSymbol b -> Maybe (b :~: a)
matches b@(SSymbol ) =  case sing @a of
  SSymbol -> sameSymbol b (SSymbol @a)

-- infixr 0 :%->
-- pattern SZ         = STCon "Z"      []
-- pattern a :%-> b   = STCon "->"     [a, b]
-- pattern SLazy a    = STCon "Lazy"   (SCons a SNil)
-- pattern STuple a b = STCon "Tuple"  [a,b]
-- pattern STop       = STCon "Top"    []
-- pattern SBot       = STCon "Bot"    []
-- pattern SF         = STCon "F"      []
-- pattern SZString   = STCon "String" []
-- pattern SZBool     = STCon "Bool"   []
-- pattern SZNull     = STCon "Null"   []
-- pattern SZDouble   = STCon "F" []
-- pattern SZInfer    = STCon "Infer"  []
-- pattern SLazyS a   = STCon "Lazy*"  [a]
-- pattern SZArray a  = STCon "Array" [a]
--

-- type (-->) a b = 'PTCon "->" [a,b]


instance Show Types where 
  showsPrec p = \case 
    TCon a [] -> showString $ Text.unpack a
    TCon "Tuple" [a,b] -> showString "(" . shows a . showString ", " . shows b . showString ")"
    a :-> b -> showParen (p > 0) $ showsPrec 1 a . showString " => " . showsPrec 0 b
    TCon a (x:xs) 
      -> showString (Text.unpack a) . showString "<" 
      . (foldr (\arg acc -> shows arg . showString ", " . acc) (shows x) xs) 
      . showString ">"



instance SDecide PTypes where
  STCon a as %~ STCon b bs = case (a %~ b, as %~ bs) of 
    (Proved Refl, Proved Refl) -> Proved Refl
    (Disproved f,_) -> Disproved (\Refl -> f Refl)
    (_,Disproved f) -> Disproved (\Refl -> f Refl)

--------------------------
-- Singing functions
--------------------------

sUpperBound :: forall (z0 :: PTypes) (z1 :: PTypes). 
  Sing z0 -> Sing z1 -> Sing (UpperBound z0 z1)
sUpperBound a b = case toSing (upperBound (fromSing a) (fromSing b)) of 
  SomeSing s -> unsafeCoerce s


sLowerBound :: forall (z0 :: PTypes) (z1 :: PTypes). 
  Sing z0 -> Sing z1 -> Sing (LowerBound z0 z1)
sLowerBound a b = case toSing (lowerBound (fromSing a) (fromSing b)) of 
  SomeSing s -> unsafeCoerce s


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
withShow :: forall (z :: PTypes). SingI z => String
withShow = show $ fromSing (sing @z) 

-- | Injects an upper bound singleton.
withSingIUBType :: forall (z0 :: PTypes) (z1 :: PTypes) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (UpperBound z0 z1) => r) -> r
withSingIUBType f = case sUpperBound (sing @z0) (sing @z1) of
  SJust ub -> withSingI ub f
  SNothing -> f


-- | Injects a lower bound singleton.
withSingILBType :: forall (z0 :: PTypes) (z1 :: PTypes) r. 
  ( SingI z0
  , SingI z1
  ) => (SingI  (LowerBound z0 z1) => r) -> r
withSingILBType f = case sLowerBound (sing @z0) (sing @z1) of
  SJust ub -> withSingI ub f
  SNothing -> f


withSingIFtype :: forall a r. SingI a => (SingI (Ftype a) => r) -> r
withSingIFtype f = case toSing (ftype (demote @a)) of 
  SomeSing s -> 
    let s' :: Sing (Ftype a) = unsafeCoerce s in withSingI s' $ f

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

ftypeIsSubtype :: forall a r. SingI a => (((UpperBound a (Ftype a) == Just a) ~ True) => r) -> r
ftypeIsSubtype f 
  = withSingIFtype @a $ case sUpperBound (sing @a) (sing @(Ftype a)) %== SJust (sing @a) of 
    STrue -> f
    SFalse -> error "impossible case"
  
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
  $ case sing @(UpperBound a b) of 
    SJust x -> withSingI x 
      $ withSingIFtype @x 
      $ case decideEquality (sUpperBound (sing @(Ftype a)) (sing @(Ftype b))) (sing @(Just (Ftype x))) of 
        Just Refl -> f
        Nothing -> error "impossible case"

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



--------------------------
-- Properties
--------------------------

{-| Upperbound being a meet, is axiomatically commutative. 

\[a \vee b = b \vee a\]
-}
ubIsCommutative :: forall (a :: PTypes) (b :: PTypes) cont.
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

ubIsCommutative' :: forall (a :: PTypes) (b :: PTypes) cont.
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




{-| Upperbound being a meet, is axiomatically associative. 

\[a \vee b = b \vee a\]
-}
ubIsAssociative :: forall {r1 :: Maybe PTypes} {r2 :: Maybe PTypes} (a :: PTypes) (b :: PTypes) (c :: PTypes) cont.
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
    $ case decideEquality' @(UpperBound c x) @(UpperBound a y) of
      Just Refl -> Just f
      Nothing -> Nothing
  _ -> Nothing

{-| Upperbound being a meet, is axiomatically reflexive. 

\[a \vee a = a\]
-}
ubIsIdempotent :: forall (a :: PTypes) cont.
  (SingI a)
  => (UpperBound a a ~ Just a => cont) -> cont
ubIsIdempotent !f = withSingIUBType @a @a $ case decideEquality (sing @(UpperBound a a)) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"


lbIsIdempotent :: forall (a :: PTypes) cont.
  (SingI a)
  => (LowerBound a a ~ Just a => cont) -> cont
lbIsIdempotent f = withSingILBType @a @a $ case decideEquality (sing @(LowerBound a a)) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"



{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = b\]
-}
ubIsTransitive'
  :: forall {r0 :: PTypes} a b c cont.
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
  :: forall {r0 :: PTypes} (f :: PTypes -> PTypes) (a :: PTypes) (b :: PTypes) cont. 
  ( UpperBound (f a) (f b) ~ Just (f r0)
  , SingI a 
  , SingI b
  , SingI r0
  ) => (UpperBound a b ~ Just r0 => cont) -> cont
ubIsInjective f =  withSingIUBType @a @b $ case decideEquality (sing @(UpperBound a b)) (sing @(Just r0)) of
  Just Refl -> f 
  Nothing   -> error "impossible case"


ubIsInjective'
  :: forall  (f :: PTypes -> PTypes) (a :: PTypes) (b :: PTypes) cont. 
  ( UpperBound (f a) (f b) ~ Nothing 
  , SingI a 
  , SingI b
  ) => (UpperBound a b ~ Nothing => cont) -> cont
ubIsInjective' f =  withSingIUBType @a @b $ case decideEquality (sing @(UpperBound a b)) (sing @Nothing) of
  Just Refl -> f 
  Nothing   -> error "impossible case"

ubPreservesFunctionForm :: forall arg body y c cont. 
  ( (UpperBound (arg --> body) y == Just c) ~ True
  , SingI y
  ) => (forall arg' body'. (y ~ (arg' --> body'), SingI arg', SingI body') => cont) -> cont 
ubPreservesFunctionForm f = case sing @y of 
  STCon n (SCons @_ @a a (SCons @_ @b b SNil)) -> case n of 
    SSymbol -> case sameSymbol n (SSymbol @"->") of 
      Just Refl -> withSingI a $ withSingI b $ f @a @b
      Nothing -> error "impossible case"
  _ -> error "impossible case"

ubPreservesFunctionForm' :: forall x y c arg body cont. 
  ( x ~ (arg --> body)
  , (UpperBound x y == Just c ) ~ True
  , SingI y
  , SingI x
  ) => (forall arg' body'. (y ~ (arg' --> body'), SingI arg', SingI body') => cont) -> cont 
ubPreservesFunctionForm' f 
  = case sing @x of
    STCon n (SCons arg (SCons body SNil)) -> case sameSymbol n (SSymbol @"->") of
      Just Refl 
        -> withSingI arg 
        $ withSingI body 
        $ withSingIUBType @x @y
        $ withSingIUBType @(arg --> body) @y
        $ eqLeibniz @(UpperBound x y) @(Just c) @(UpperBound (arg --> body) y)
        $ ubPreservesFunctionForm @arg @body @y @c $ f
      _ -> error "impossible case"




{-| Convinient "transitive" property... For the time being taken as axiom... 
TODO: Make a proof, just another take on associativity.

\[a \vee b = c\]
\[a \vee c = c\]
-}
ubIsUb :: forall (a :: PTypes) (b :: PTypes) (r0 :: PTypes) cont.
  ( UpperBound a b ~ Just r0 
  , SingI a
  , SingI b
  , SingI r0
  ) 
  => (UpperBound a r0 ~ Just r0 => cont) -> cont
ubIsUb !f =  withSingIUBType @a @r0 $  case decideEquality (sing @(UpperBound a r0 )) (sing @(Just r0)) of
  Just Refl -> f
  Nothing -> error "impossible case"

---------------------
-- Upcasting
---------------------

data UpperBoundResults f a b where
  NonExistentUB   :: (UpperBound a b ~ Nothing) => UpperBoundResults f a b 
  SameTypeUB      :: (a ~ b, UpperBound a b ~ Just a, UpperBound a b ~ Just b) => f a -> UpperBoundResults f a b 
  LeftUB          :: (UpperBound a b ~ Just a)  => f a -> UpperBoundResults f a b 
  RightUB         :: (UpperBound a b ~ Just b)  => f b -> UpperBoundResults f a b 
  SomethingElseUB :: forall (r :: PTypes) f (a :: PTypes) (b :: PTypes) . 
    ( UpperBound a b ~ Just r
    , SingI r
    ) => f r -> UpperBoundResults f a b 

data LowerBoundResults f a b where
  NonExistentLB   :: (LowerBound a b ~ Nothing) => LowerBoundResults f a b 
  SameTypeLB      :: (a ~ b, LowerBound a b ~ Just a, LowerBound a b ~ Just b) => f a -> LowerBoundResults f a b 
  LeftLB          :: (LowerBound a b ~ Just a)  => f a -> LowerBoundResults f a b 
  RightLB         :: (LowerBound a b ~ Just b)  => f b -> LowerBoundResults f a b 
  SomethingElseLB :: forall (r :: PTypes) f (a :: PTypes) (b :: PTypes) . 
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
    (a :: PTypes) 
    (b :: PTypes).
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
    (a :: PTypes) 
    (b :: PTypes).
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


