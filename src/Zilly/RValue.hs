
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE CPP                      #-}

{-# LANGUAGE TemplateHaskell          #-}

{-|
Module      : Zilly.RValue
Description : Definition of RValue and evidence injection for Zilly.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Defines the RValue class, provides a way to inject them RValue types into a continuation..
-}
module Zilly.RValue where 

import qualified Data.Proof as P
import Zilly.Types
import Zilly.ADT.Expression
import qualified Data.Proof as Proof
import Data.Singletons
import Data.Singletons.Decide
import Data.Kind (Type)
import Data.Singletons.TH  hiding (Const)
$(singletons [d| 
  rValueT :: Types -> Types
  rValueT (Value a) = Value a
  rValueT (Array a) = Array (rValueT a)
  rValueT (Lazy a)  = a
  rValueT (LazyS a) = a
  |])


rLambdasArgs :: Types -> Types 
rLambdasArgs (Value (Lazy a :-> b))
  = Value (rLambdasArgs a :-> rLambdasArgs b)
rLambdasArgs (Value (a :->  b))
  = Value (rLambdasArgs a :-> rLambdasArgs b)
rLambdasArgs a = a




{- |
Class that yields the rvalue of a given type. 
-}
class RValue (ctx :: Type) (a :: Types)  where
  rvalue :: E ctx a -> (AssocCtxMonad ctx) (E ctx (RValueT a))

{- -- same issue, illegal type family declaration....
type RTypeAxioms f =
  ( forall (a :: Types0) (b :: Types). RValueT f (Value a) ~ RValueT f (Value a)
  , forall (a :: Types). RValue f a
  ) -}

-- | Whenever we know a type, we know its rvalue-dict
withRVType :: forall (ctx :: Type) (z :: Types)  r.
  ( forall (a :: Types).  RValue ctx (Lazy (Lazy a)) 
  , forall (a :: Types0). RValue ctx (Lazy (Value a)) 
  , forall (a :: Types0). RValue ctx (Value a) 
  ) => Sing z -> (RValue ctx z  => r) -> r
withRVType (SValue v) f = case v of
  (SZ :: Sing (x :: Types0)) -> f
  (z1 :%-> z2) -> withRVType @ctx z1 $ withRVType @ctx z2 f
withRVType (SLazy  (SLazy s)) f = withRVType @ctx s f
withRVType (SLazy (SValue s)) f = withSingI s $ withRVType @ctx (SValue s) f
withRVType _ _ = error "Lazy* not supported"

-- | Whenever we know a type, we know its rtype
withSingIRType :: forall (z :: Types) cont. SingI z => (SingI  (RValueT z) => cont) -> cont
withSingIRType f 
  = case sing @z of
  (SValue @n _) -> case decideEquality' @_ @(Value n) @(RValueT z) of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT z) @n of
    Just Refl -> f
    Nothing -> error "Type mismatch"
  (SLazyS @n sa)   -> error "Lazy* not implemented"
  SLazy (SLazyS _) -> error "Lazy* not implemented"

-- | Whenever we know two types, whe know their meet.
rvaluePreservesST :: forall {r0 :: Types} a b cont. 
  ( SingI a
  , SingI b
  , SingI r0
  , UpperBound a b ~ Just r0
  ) 
  => (UpperBound (RValueT a) (RValueT b) ~ Just (RValueT r0) => cont) -> cont
rvaluePreservesST f
  = withSingIRType @a 
  $ withSingIRType @b 
  $ withSingIRType @r0
  $ withSingIUBType @(RValueT a) @(RValueT b)
  $ case decideEquality' @_ @(UpperBound (RValueT a) (RValueT b)) @(Just (RValueT r0))of
    Just Refl -> f
    Nothing -> error "impossible case"

{-| Whenever we know a type \(a\), we know that:

  \[a \vee rtype(a) = a\]

-}
rvalueIsPred :: forall (a :: Types) cont.
  ( SingI a
  )
  => (UpperBound (RValueT a) a ~ Just a => cont) -> cont
rvalueIsPred !f 
  = withSingIRType @a
  $ withSingIUBType @(RValueT a) @a 
  $ case  decideEquality (sing @(UpperBound (RValueT a) a )) (sing @(Just a)) of
  Just Refl -> f
  Nothing -> error "impossible case"
{- rvalueIsPred !f 
  = case sing @a of
    (SValue @n SZ) -> case sing @(RValueT (Value n)) of 
      SValue @m SZ -> f
    (SValue @n (a :%-> b)) -> case sing @(RValueT (Value n)) of 
      SValue @m (a' :%-> b') -> f
      
    (SLazy @n sa@(SLazy _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT a) @n of
      Just Refl -> undefined
      Nothing -> error "Type mismatch"
    (SLazy @n sa@(SValue _)) -> withSingI @n sa $ case decideEquality' @_ @(RValueT a) @n of
      Just Refl -> undefined
      Nothing -> error "Type mismatch"
    (SLazyS @n sa)   -> error "Lazy* not implemented"
    SLazy (SLazyS _) -> error "Lazy* not implemented" -}

-- | An easy way of constructing the subtyped context.
subtyped'CTX :: forall {r :: Types} ctx (a :: Types) (b :: Types)  cont.
  ( SingI a
  , SingI b
  , SingI r
  , UpperBound a b ~ 'Just r
  , forall (z :: Types).  RValue ctx (Lazy (Lazy z)) 
  , forall (z :: Types0). RValue ctx (Lazy (Value z)) 
  , forall (z :: Types0). RValue ctx (Value z) 
  ) => ((UpperBound (RValueT a) r ~ 'Just r, RValue ctx a, RValue ctx b) => cont) -> cont
subtyped'CTX f 
  = withSingIRType @a  
  $ withSingIRType @b 
  $ withRVType @ctx (sing @a)  
  $ withRVType @ctx (sing @b) 
  $ rvalueIsPred @a
  $ ubIsUb @a @b
  $ ubIsTransitive' @(RValueT a) @a @r
  $ f

typesCaseAnalysisRV :: forall (ctx :: Type) (x :: Types).
  ( TypesCaseAnalysis (RValue ctx)
  , SingI x 
  ) => P.Dict (RValue ctx x)
typesCaseAnalysisRV = typesCaseAnalysis @(RValue ctx) @x

withRV :: forall (ctx :: Type) (x :: Types) c.
  ( TypesCaseAnalysis (RValue ctx)
  , SingI x 
  ) => (RValue ctx x => c) -> c
withRV f = case typesCaseAnalysisRV @ctx @x of 
  Proof.Dict -> f
{- 
upcastable :: forall (a :: Types) (b :: Types). 
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
            -> withRVType (sing @a)
            $  rvalueIsPred @a
            $  withSingI sub 
            $  SomethingElseUBN @a @b
      SNothing  -> NonExistentUB

data UpperBoundResults (f :: Types -> Type) (a :: Types) (b :: Types)where
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


lazyRT :: forall a f cont. 
  (SingI a
  , forall (b :: Types). RValue f b
  ) 
  => (RValueT f (Lazy a) ~ a => cont) -> cont
lazyRT f = case sing @a of
  sl@(SLazy @n _)  -> f
  sv@(SValue @n _) -> f
  sls@(SLazyS _) -> error "Lazy* not implemented"

 -}


