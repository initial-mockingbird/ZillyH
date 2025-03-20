{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE TemplateHaskell            #-}

{-|
Module      : Zilly.Classic.Expression
Description : Defines the contexts of expressions and its rvalue rules for classic zilly.
Copyright   : (c) Daniel Dictinto, 2024
                  Enzo Alda, 2024
License     : GDictL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Dictortability : DictOSIX

-}
module Zilly.ZillyPlus.Arithmetic where

import Data.Proof
import Utilities.LensM
import Utilities.TypedMapPlus
import Zilly.Types
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Arithmetic
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter
import Zilly.ZillyPlus.Expression
import Control.Monad 

import Control.Applicative

import Utilities.ShowM
import Prelude hiding (LT,GT,EQ)
import Prelude.Singletons (SingI(..),Sing,SMaybe(..),withSingI)
import Data.Sequence 
import Data.Kind (Type)

import Data.Singletons.TH (singletons)

$(singletons [d|
  data ArithOpTags 
    = PlusTag
    | MinusTag
    | TimesTag
    | DivTag 
    | ModTag 
    | PowerTag
    | UMinusTag

  |])


--------------------------
-- Util functions 
--------------------------


------------------------
-- Types and instances- 
------------------------


data ArithmeticTag

type family ArithNumType (a :: Types) :: Type where
  ArithNumType (Value Z) = Int 
  ArithNumType (Value F) = Double 
  ArithNumType (Array a) = Seq (ArithNumType a)


class
  ( 
  ) =>
  BinOp (tag :: ArithOpTags)  (a :: Types) (b :: Types) where 
    type BinOpReturn (tag :: ArithOpTags) (a :: Types) (b :: Types) :: Types

    (***) ::() -- (ArithBaseType (BinOpReturn tag a b))
      => ArithNumType a 
      -> ArithNumType b
      -> (AssocCtxMonad ArithmeticTag) (ArithNumType (BinOpReturn tag a b))

class UOp (tag :: ArithOpTags) (a :: Types) where 
  type UOpReturn (tag :: ArithOpTags) (a :: Types) :: Types 
  unaryOp :: ArithNumType a -> (AssocCtxMonad ArithmeticTag) (ArithNumType (UOpReturn tag a))

type family Pointwise (a :: Types) (b :: Types) :: Types where 
  Pointwise (Value Z) (Value Z) = Value Z 
  Pointwise (Value Z) (Value F) = Value F 
  Pointwise (Value F) (Value Z) = Value F
  Pointwise (Value F) (Value F) = Value F
  Pointwise (Array a) (Value b) = Array (Pointwise a (Value b))
  Pointwise (Value b) (Array a) = Array (Pointwise (Value b) a)
  Pointwise (Array a) (Array b) = Array (Pointwise a b)

--------------------------------------
-- Addition
-- -----------------------------------

instance BinOp PlusTag (Value F) (Value F) where 
  type BinOpReturn PlusTag (Value F) (Value F) = Value F 

  a *** b = pure $ a + b

instance BinOp PlusTag (Value Z) (Value Z) where 
  type BinOpReturn PlusTag (Value Z) (Value Z) = Value Z

  a *** b = pure $ a + b

instance BinOp PlusTag (Value Z) (Value F) where 
  type BinOpReturn PlusTag (Value Z) (Value F) = Value F 

  a *** b = pure $ fromIntegral a + b

instance BinOp PlusTag (Value F) (Value Z) where 
  type BinOpReturn PlusTag (Value F) (Value Z) = Value F 

  a *** b = pure $ a + fromIntegral b

instance 
  ( BinOp PlusTag a (Value b)
  , BinOpReturn PlusTag a (Value b) ~ Pointwise a (Value b) 
  ) =>  BinOp PlusTag (Array a) (Value b) where 
  type BinOpReturn PlusTag (Array a) (Value b) = Pointwise (Array a) (Value b)

  as *** b = traverse (\a -> (***) @PlusTag @a @(Value b) a b) as

instance 
  ( BinOp PlusTag (Value a) b
  , BinOpReturn PlusTag (Value a) b ~ Pointwise (Value a) b
  ) =>  BinOp PlusTag (Value a) (Array b) where 
  type BinOpReturn PlusTag (Value a) (Array b) = Pointwise (Value a) (Array b)

  a *** bs = traverse ((***) @PlusTag @(Value a) @b a) bs

instance 
  ( BinOp PlusTag a b
  -- , ArithBaseType (BinOpReturn PlusTag a b)
  ) =>  BinOp PlusTag (Array a) (Array b) where 
  type BinOpReturn PlusTag (Array a) (Array b) = Array (BinOpReturn PlusTag a b)

  as *** bs = sequence $ Data.Sequence.zipWith ((***) @PlusTag @a @b) as bs

--------------------------------------
-- Substraction
-- -----------------------------------

instance BinOp MinusTag (Value F) (Value F) where 
  type BinOpReturn MinusTag (Value F) (Value F) = Value F 

  a *** b = pure $ a - b

instance BinOp MinusTag (Value Z) (Value Z) where 
  type BinOpReturn MinusTag (Value Z) (Value Z) = Value Z

  a *** b = pure $ a - b

instance BinOp MinusTag (Value Z) (Value F) where 
  type BinOpReturn MinusTag (Value Z) (Value F) = Value F 

  a *** b = pure $ fromIntegral a - b

instance BinOp MinusTag (Value F) (Value Z) where 
  type BinOpReturn MinusTag (Value F) (Value Z) = Value F 

  a *** b = pure $ a - fromIntegral b

instance 
  ( BinOp MinusTag a (Value b)
  , BinOpReturn MinusTag a (Value b) ~ Pointwise a (Value b) 
  ) =>  BinOp MinusTag (Array a) (Value b) where 
  type BinOpReturn MinusTag (Array a) (Value b) = Pointwise (Array a) (Value b)

  as *** b = traverse (\a -> (***) @MinusTag @a @(Value b) a b) as

instance 
  ( BinOp MinusTag (Value a) b
  , BinOpReturn MinusTag (Value a) b ~ Pointwise (Value a) b
  ) =>  BinOp MinusTag (Value a) (Array b) where 
  type BinOpReturn MinusTag (Value a) (Array b) = Pointwise (Value a) (Array b)

  a *** bs = traverse ((***) @MinusTag @(Value a) @b a) bs

instance 
  ( BinOp MinusTag a b
  -- , ArithBaseType (BinOpReturn MinusTag a b)
  ) =>  BinOp MinusTag (Array a) (Array b) where 
  type BinOpReturn MinusTag (Array a) (Array b) = Array (BinOpReturn MinusTag a b)

  as *** bs = sequence $ Data.Sequence.zipWith ((***) @MinusTag @a @b) as bs

--------------------------------------
-- Multiplication
-- -----------------------------------

instance BinOp TimesTag (Value F) (Value F) where 
  type BinOpReturn TimesTag (Value F) (Value F) = Value F 

  a *** b = pure $ a * b

instance BinOp TimesTag (Value Z) (Value Z) where 
  type BinOpReturn TimesTag (Value Z) (Value Z) = Value Z

  a *** b = pure $ a * b

instance BinOp TimesTag (Value Z) (Value F) where 
  type BinOpReturn TimesTag (Value Z) (Value F) = Value F 

  a *** b = pure $ fromIntegral a * b

instance BinOp TimesTag (Value F) (Value Z) where 
  type BinOpReturn TimesTag (Value F) (Value Z) = Value F 

  a *** b = pure $ a * fromIntegral b

instance 
  ( BinOp TimesTag a (Value b)
  , BinOpReturn TimesTag a (Value b) ~ Pointwise a (Value b) 
  ) =>  BinOp TimesTag (Array a) (Value b) where 
  type BinOpReturn TimesTag (Array a) (Value b) = Pointwise (Array a) (Value b)

  as *** b = traverse (\a -> (***) @TimesTag @a @(Value b) a b) as

instance 
  ( BinOp TimesTag (Value a) b
  , BinOpReturn TimesTag (Value a) b ~ Pointwise (Value a) b
  ) =>  BinOp TimesTag (Value a) (Array b) where 
  type BinOpReturn TimesTag (Value a) (Array b) = Pointwise (Value a) (Array b)

  a *** bs = traverse ((***) @TimesTag @(Value a) @b a) bs

instance 
  ( BinOp TimesTag a b
  -- , ArithBaseType (BinOpReturn TimesTag a b)
  ) =>  BinOp TimesTag (Array a) (Array b) where 
  type BinOpReturn TimesTag (Array a) (Array b) = Array (BinOpReturn TimesTag a b)

  as *** bs = sequence $ Data.Sequence.zipWith ((***) @TimesTag @a @b) as bs


--------------------------------------
-- Division
-- -----------------------------------

instance BinOp DivTag (Value F) (Value F) where 
  type BinOpReturn DivTag (Value F) (Value F) = Value F 

  _ *** 0 = error "TODO"
  a *** b = pure $ a / b

instance BinOp DivTag (Value Z) (Value Z) where 
  type BinOpReturn DivTag (Value Z) (Value Z) = Value F

  _ *** 0 = error "TODO"
  a *** b = pure $ fromIntegral a / fromIntegral b

instance BinOp DivTag (Value Z) (Value F) where 
  type BinOpReturn DivTag (Value Z) (Value F) = Value F 

  _ *** 0 = error "TODO"
  a *** b = pure $ fromIntegral a / b

instance BinOp DivTag (Value F) (Value Z) where 
  type BinOpReturn DivTag (Value F) (Value Z) = Value F 

  _ *** 0 = error "TODO"
  a *** b = pure $ a / fromIntegral b

instance 
  ( BinOp DivTag a (Value b)
  ) =>  BinOp DivTag (Array a) (Value b) where 
  type BinOpReturn DivTag (Array a) (Value b) = Array (BinOpReturn DivTag a (Value b))

  as *** b = traverse (\a -> (***) @DivTag @a @(Value b) a b) as

instance 
  ( BinOp DivTag (Value a) b
  ) =>  BinOp DivTag (Value a) (Array b) where 
  type BinOpReturn DivTag (Value a) (Array b) = Array (BinOpReturn DivTag (Value a) b)

  a *** bs = traverse ((***) @DivTag @(Value a) @b a) bs

instance 
  ( BinOp DivTag a b
  ) =>  BinOp DivTag (Array a) (Array b) where 
  type BinOpReturn DivTag (Array a) (Array b) = Array (BinOpReturn DivTag a b)

  as *** bs = sequence $ Data.Sequence.zipWith ((***) @DivTag @a @b) as bs

--------------------------------------
-- Modulo
-- -----------------------------------

instance BinOp ModTag (Value Z) (Value Z) where 
  type BinOpReturn ModTag (Value Z) (Value Z) = Value Z

  _ *** 0 = error "TODO"
  a *** b = pure $ mod a b

instance 
  ( BinOp ModTag a (Value Z)
  ) =>  BinOp ModTag (Array a) (Value Z) where 
  type BinOpReturn ModTag (Array a) (Value Z) = Array (BinOpReturn ModTag a (Value Z))

  as *** b = traverse (\a -> (***) @ModTag @a @(Value Z) a b) as

instance 
  ( BinOp ModTag (Value Z) b
  ) =>  BinOp ModTag (Value Z) (Array b) where 
  type BinOpReturn ModTag (Value Z) (Array b) = Array (BinOpReturn ModTag (Value Z) b)

  a *** bs = traverse ((***) @ModTag @(Value Z) @b a) bs

instance 
  ( BinOp ModTag a b
  ) =>  BinOp ModTag (Array a) (Array b) where 
  type BinOpReturn ModTag (Array a) (Array b) = Array (BinOpReturn ModTag a b)

  as *** bs = sequence $ Data.Sequence.zipWith ((***) @ModTag @a @b) as bs

--------------------------------------
-- Exponentiation
-- -----------------------------------

instance BinOp PowerTag (Value F) (Value F) where 
  type BinOpReturn PowerTag (Value F) (Value F) = Value F 

  0 *** 0 = error "TODO"
  a *** b = pure $ a ** b

instance BinOp PowerTag (Value Z) (Value Z) where 
  type BinOpReturn PowerTag (Value Z) (Value Z) = Value Z

  0 *** 0 = error "TODO"
  a *** b = pure $ a ^ b

instance BinOp PowerTag (Value Z) (Value F) where 
  type BinOpReturn PowerTag (Value Z) (Value F) = Value F 

  0 *** 0 = error "TODO"
  a *** b = pure $ fromIntegral a ** b

instance BinOp PowerTag (Value F) (Value Z) where 
  type BinOpReturn PowerTag (Value F) (Value Z) = Value F 

  0 *** 0 = error "TODO"
  a *** b = pure $ a ** fromIntegral b

instance 
  ( BinOp PowerTag a (Value b)
  ) =>  BinOp PowerTag (Array a) (Value b) where 
  type BinOpReturn PowerTag (Array a) (Value b) = Array (BinOpReturn PowerTag a (Value b))

  as *** b = traverse (\a -> (***) @PowerTag @a @(Value b) a b) as

instance 
  ( BinOp PowerTag (Value a) b
  ) =>  BinOp PowerTag (Value a) (Array b) where 
  type BinOpReturn PowerTag (Value a) (Array b) = Array (BinOpReturn PowerTag (Value a) b)

  a *** bs = traverse ((***) @PowerTag @(Value a) @b a) bs



----------------------------------
-- Pointwise CPS 
-- -------------------------------


withSingIPointwise :: forall a b r. 
  (SingI a, SingI b) => (SingI (Pointwise a b) => r) -> Maybe r
withSingIPointwise f = case (sing @a, sing @b) of
  (SValue SZ, SValue SZ) -> pure f
    
  (SValue SZ, SValue SF) -> pure f
    
  (SValue SF, SValue SZ) -> pure f
    
  (SValue SF, SValue SF) -> pure f

  (SArray @x x, SValue _) -> withSingI x $ withSingIPointwise @x @b f

  (SValue _, SArray @x x) -> withSingI x $ withSingIPointwise @a @x f

  (SArray @x x, SArray @y y) 
    -> withSingI x 
    $  withSingI y
    $ withSingIPointwise @x @y f 

  _ -> Nothing


withSingIOpReturn :: forall tag a b r.
  (SingI a, SingI b, SingI tag) => (SingI (BinOpReturn tag a b) => r) -> Maybe r
withSingIOpReturn f = case (sing @a, sing @b) of
  (SValue SZ, SValue SZ) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> pure f 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing
    
  (SValue SZ, SValue SF) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing
    
  (SValue SF, SValue SZ) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing
    SPowerTag -> pure f 
    SUMinusTag -> Nothing

    
  (SValue SF, SValue SF) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing


  (SArray @x x, SValue _) 
    -> join 
    $ withSingI x 
    $ withSingIPointwise @x @b
    $ case sing @tag of 
      SPlusTag  -> withSingIOpReturn @tag @x @b f 
      SMinusTag -> withSingIOpReturn @tag @x @b f 
      STimesTag -> withSingIOpReturn @tag @x @b f 
      SDivTag   -> withSingIOpReturn @tag @x @b f 
      SModTag   -> Nothing 
      SPowerTag -> withSingIOpReturn @tag @x @b f 
      SUMinusTag -> Nothing


  (SValue _, SArray @x x) 
    -> join 
    $ withSingI x 
    $ withSingIPointwise @a @x
    $ case sing @tag of 
      SPlusTag  -> withSingIOpReturn @tag @a @x f 
      SMinusTag -> withSingIOpReturn @tag @a @x f 
      STimesTag -> withSingIOpReturn @tag @a @x f 
      SDivTag   -> withSingIOpReturn @tag @a @x f 
      SModTag   -> Nothing 
      SPowerTag -> withSingIOpReturn @tag @a @x f 
      SUMinusTag -> Nothing


  (SArray @x x, SArray @y y) 
    -> join 
    $ withSingI x 
    $  withSingI y
    $ withSingIPointwise @x @y 
    $ case sing @tag of 
      SPlusTag  -> withSingIOpReturn @tag @x @y f 
      SMinusTag -> withSingIOpReturn @tag @x @y f 
      STimesTag -> withSingIOpReturn @tag @x @y f 
      SDivTag   -> withSingIOpReturn @tag @x @y f 
      SModTag   -> Nothing 
      SPowerTag -> Nothing 
      SUMinusTag -> Nothing


  _ -> Nothing

isBinOpReturnPointwise :: forall tag a b r.
  (SingI tag, SingI a, SingI b) => (BinOpReturn tag a b ~ Pointwise a b => r) -> Maybe r
isBinOpReturnPointwise f = case sing @tag of 
  SPlusTag -> case (sing @a, sing @b) of
    (SValue SZ, SValue SZ) -> pure f
      
    (SValue SZ, SValue SF) -> pure f
      
    (SValue SF, SValue SZ) -> pure f
      
    (SValue SF, SValue SF) -> pure f
    
    (SArray @x x, SValue _)
      -> withSingI x 
      $ isBinOpReturnPointwise @tag @x @b
      $ f

    (SValue _, SArray @x x)
      -> withSingI x
      $ isBinOpReturnPointwise @tag @a @x 
      $ f

    (SArray @x x, SArray @y y)
      -> withSingI x
      $ withSingI y
      $ isBinOpReturnPointwise @tag @x @y
      $ f

    _ -> Nothing

  _ -> Nothing

withBinOp ::forall tag a b r. 
  (SingI a, SingI b, SingI tag) => ( BinOp tag a b => r) -> Maybe r
withBinOp f = case (sing @a, sing @b) of
  (SValue SZ, SValue SZ) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> pure f 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing
    
  (SValue SZ, SValue SF) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing
    
  (SValue SF, SValue SZ) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing
    SPowerTag -> pure f 
    SUMinusTag -> Nothing

    
  (SValue SF, SValue SF) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing


  (SArray @x x, SValue _) 
    -> join 
    $ join
    $ withSingI x
    $ withSingIOpReturn @tag @x @b
    $ isBinOpReturnPointwise @tag @x @b
    $ case sing @tag of 
      SPlusTag  -> withBinOp @tag @x @b f 
      SMinusTag -> withBinOp @tag @x @b f 
      STimesTag -> withBinOp @tag @x @b f 
      SDivTag   -> withBinOp @tag @x @b f 
      SModTag   -> Nothing 
      SPowerTag -> withBinOp @tag @x @b f 
      SUMinusTag -> Nothing

    
  (SValue _, SArray @x x) 
    -> join 
    $ join
    $ withSingI x
    $ withSingIOpReturn @tag @a @x
    $ isBinOpReturnPointwise @tag @a @x
    $ case sing @tag of 
      SPlusTag  -> withBinOp @tag @a @x f 
      SMinusTag -> withBinOp @tag @a @x f 
      STimesTag -> withBinOp @tag @a @x f 
      SDivTag   -> withBinOp @tag @a @x f 
      SModTag   -> Nothing 
      SPowerTag -> withBinOp @tag @a @x f 
      SUMinusTag -> Nothing

  (SArray @x x, SArray @y y) 
    -> join 
    $ withSingI x
    $ withSingI y
    $ withSingIOpReturn @tag @x @y
    $ case sing @tag of 
      SPlusTag  -> withBinOp @tag @x @y f 
      SMinusTag -> withBinOp @tag @x @y f 
      STimesTag -> withBinOp @tag @x @y f 
      SDivTag   -> withBinOp @tag @x @y f 
      SModTag   -> Nothing 
      SPowerTag -> Nothing
      SUMinusTag -> Nothing

  _ -> Nothing

withBinOpPointwise ::forall tag a b r. 
  (SingI a, SingI b, SingI tag) => ( BinOp tag a b => r) -> Maybe r
withBinOpPointwise f = case (sing @a, sing @b) of
  (SValue SZ, SValue SZ) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> pure f 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing
    
  (SValue SZ, SValue SF) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing
    
  (SValue SF, SValue SZ) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing

    
  (SValue SF, SValue SF) -> case sing @tag of 
    SPlusTag  -> pure f 
    SMinusTag -> pure f 
    STimesTag -> pure f 
    SDivTag   -> pure f 
    SModTag   -> Nothing 
    SPowerTag -> pure f 
    SUMinusTag -> Nothing


  (SArray @x x, SValue _) 
    -> join 
    $ join
    $ withSingI x
    $ withSingIOpReturn @tag @x @b
    $ isBinOpReturnPointwise @tag @x @b
    $ case sing @tag of 
      SPlusTag  -> withBinOpPointwise @tag @x @b f 
      SMinusTag -> withBinOpPointwise @tag @x @b f 
      STimesTag -> withBinOpPointwise @tag @x @b f 
      SDivTag   -> withBinOpPointwise @tag @x @b f 
      SModTag   -> Nothing
      SPowerTag -> withBinOpPointwise @tag @x @b f 
      SUMinusTag -> Nothing

  (SValue _, SArray @x x) 
    -> join 
    $ join
    $ withSingI x
    $ withSingIOpReturn @tag @a @x
    $ isBinOpReturnPointwise @tag @a @x
    $ case sing @tag of 
      SPlusTag  -> withBinOpPointwise @tag @a @x f 
      SMinusTag -> withBinOpPointwise @tag @a @x f 
      STimesTag -> withBinOpPointwise @tag @a @x f 
      SDivTag   -> withBinOpPointwise @tag @a @x f 
      SModTag   -> Nothing
      SPowerTag -> withBinOpPointwise @tag @a @x f 
      SUMinusTag -> Nothing

  (SArray @x x, SArray @y y) 
    -> join 
    $ withSingI x
    $ withSingI y
    $ withSingIOpReturn @tag @x @y    
    $ case sing @tag of 
      SPlusTag  -> withBinOpPointwise @tag @x @y f 
      SMinusTag -> withBinOpPointwise @tag @x @y f 
      STimesTag -> withBinOpPointwise @tag @x @y f 
      SDivTag   -> withBinOpPointwise @tag @x @y f 
      SModTag   -> Nothing
      SPowerTag -> Nothing
      SUMinusTag -> Nothing

  _ -> Nothing


--------------------------------------
-- Negation
-- -----------------------------------

instance UOp UMinusTag (Value Z) where 
  type UOpReturn UMinusTag (Value Z) = Value Z
  unaryOp = pure . negate

instance UOp UMinusTag (Value F) where 
  type UOpReturn UMinusTag (Value F) = Value F
  unaryOp = pure . negate

instance (UOp UMinusTag a) => UOp UMinusTag (Array a) where 
  type UOpReturn UMinusTag (Array a) = Array (UOpReturn UMinusTag a)
  unaryOp = traverse (unaryOp @UMinusTag @a) 

withUOp :: forall tag a r. 
  ( SingI tag 
  , SingI a
  ) => ( (UOp tag a, UOpReturn tag a ~ a) => r) -> Maybe r
withUOp f = case sing @tag of 
  SUMinusTag -> case sing @a of 
    SValue SZ -> pure f
    SValue SF -> pure f 
    SArray @sa sa -> withSingI sa $ withUOp @tag @sa f
    _ -> Nothing
  _ -> Nothing

class 
  ( -- ArithBaseType a 
  )
  => Biject (f :: Types -> Type) (a :: Types) where 

    project :: f a -> (AssocCtxMonad ArithmeticTag) (ArithNumType a)
    inject  :: ArithNumType a -> (AssocCtxMonad ArithmeticTag) (f a)



data LCA a where 
  MkLCA :: a ~ RValueT b => Sing b -> LCA a
 
lca :: forall a. SingI a => LCA a
lca = case sing @a of 
  SValue a -> MkLCA $ SValue a 
  SLazy a  -> MkLCA $ SLazy (SLazy a)
  SLazyS a -> MkLCA $ SLazyS a
  SArray @x x -> withSingI x $  case lca @x of 
    MkLCA x' -> MkLCA $ SArray x'


type instance AssocCtxMonad ArithmeticTag = TaggedInterpreter ExprTag

type PointwiseDicts tag sup sub a b c =
  ( Dict (SingI a)
  , Dict (SingI b)
  , Dict (SingI c)
  , Dict (BinOp tag (RValueT a) (RValueT b))
  , Dict (Biject sup (RValueT a))
  , Dict (Biject sup (RValueT b))
  , Dict (Biject sub  (RValueT a))
  , Dict (Biject sub (RValueT b))
  , Dict (Biject sub (RValueT c))
  , Dict (Biject sup (RValueT c))
  , Dict (BinOpReturn tag (RValueT a) (RValueT b) ~ RValueT c )
  , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
  )

type instance PlusX sup sub ArithmeticTag a b c 
  = PointwiseDicts PlusTag sup sub a b c

pattern ArithPlusE :: forall sup sub c. 
  ( SingI c
  , Biject sup (RValueT c)
  , Biject sub (RValueT c)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  ) => forall a b. 
    (BinOp PlusTag (RValueT a) (RValueT b)
    , Biject sup (RValueT a)
    , Biject sup (RValueT b)
    , Biject sub (RValueT a)
    , Biject sub (RValueT b)
    , BinOpReturn PlusTag (RValueT a) (RValueT b) ~ RValueT c
    , SingI a
    , SingI b
    ) => Arithmetic sup sub ArithmeticTag a 
      -> Arithmetic sup sub ArithmeticTag b 
      -> Arithmetic sup sub ArithmeticTag c 
pattern ArithPlusE a b <- Plus 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b 
    where ArithPlusE a b = Plus 
            ( Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            ) a b


type instance MinusX sup sub ArithmeticTag a b c 
  = PointwiseDicts MinusTag sup sub a b c

pattern ArithMinusE :: forall sup sub c. 
  ( SingI c
  , Biject sup (RValueT c)
  , Biject sub (RValueT c)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  ) => forall a b. 
    (BinOp MinusTag (RValueT a) (RValueT b)
    , Biject sup (RValueT a)
    , Biject sup (RValueT b)
    , Biject sub (RValueT a)
    , Biject sub (RValueT b)
    , BinOpReturn MinusTag (RValueT a) (RValueT b) ~ RValueT c
    , SingI a
    , SingI b
    ) => Arithmetic sup sub ArithmeticTag a 
      -> Arithmetic sup sub ArithmeticTag b 
      -> Arithmetic sup sub ArithmeticTag c 
pattern ArithMinusE a b <- Minus  
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b 
    where ArithMinusE a b = Minus
            ( Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            ) a b

type instance TimesX sup sub ArithmeticTag a b c 
  = PointwiseDicts TimesTag sup sub a b c

pattern ArithTimesE :: forall sup sub c. 
  ( SingI c
  , Biject sup (RValueT c)
  , Biject sub (RValueT c)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  ) => forall a b. 
    (BinOp TimesTag (RValueT a) (RValueT b)
    , Biject sup (RValueT a)
    , Biject sup (RValueT b)
    , Biject sub (RValueT a)
    , Biject sub (RValueT b)
    , BinOpReturn TimesTag (RValueT a) (RValueT b) ~ RValueT c
    , SingI a
    , SingI b
    ) => Arithmetic sup sub ArithmeticTag a 
      -> Arithmetic sup sub ArithmeticTag b 
      -> Arithmetic sup sub ArithmeticTag c 
pattern ArithTimesE a b <- Times 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b 
    where ArithTimesE a b = Times 
            ( Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            ) a b

type instance DivX sup sub ArithmeticTag a b c 
  = PointwiseDicts DivTag sup sub a b c

pattern ArithDivE :: forall sup sub c. 
  ( SingI c
  , Biject sup (RValueT c)
  , Biject sub (RValueT c)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  ) => forall a b. 
    (BinOp DivTag (RValueT a) (RValueT b)
    , Biject sup (RValueT a)
    , Biject sup (RValueT b)
    , Biject sub (RValueT a)
    , Biject sub (RValueT b)
    , BinOpReturn DivTag (RValueT a) (RValueT b) ~ RValueT c
    , SingI a
    , SingI b
    ) => Arithmetic sup sub ArithmeticTag a 
      -> Arithmetic sup sub ArithmeticTag b 
      -> Arithmetic sup sub ArithmeticTag c 
pattern ArithDivE a b <- Div 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b 
    where ArithDivE a b = Div 
            ( Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            ) a b

type instance ModX sup sub ArithmeticTag a b c 
  = PointwiseDicts ModTag sup sub a b c

pattern ArithModE :: forall sup sub c. 
  ( SingI c
  , Biject sup (RValueT c)
  , Biject sub (RValueT c)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  ) => forall a b. 
    (BinOp ModTag (RValueT a) (RValueT b)
    , Biject sup (RValueT a)
    , Biject sup (RValueT b)
    , Biject sub (RValueT a)
    , Biject sub (RValueT b)
    , BinOpReturn ModTag (RValueT a) (RValueT b) ~ RValueT c
    , SingI a
    , SingI b
    ) => Arithmetic sup sub ArithmeticTag a 
      -> Arithmetic sup sub ArithmeticTag b 
      -> Arithmetic sup sub ArithmeticTag c 
pattern ArithModE a b <- Mod 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b 
    where ArithModE a b = Mod 
            ( Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            ) a b

type instance PowerX sup sub ArithmeticTag a b c 
  = PointwiseDicts PowerTag sup sub a b c

pattern ArithPowerE :: forall sup sub c. 
  ( SingI c
  , Biject sup (RValueT c)
  , Biject sub (RValueT c)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  ) => forall a b. 
    (BinOp PowerTag (RValueT a) (RValueT b)
    , Biject sup (RValueT a)
    , Biject sup (RValueT b)
    , Biject sub (RValueT a)
    , Biject sub (RValueT b)
    , BinOpReturn PowerTag (RValueT a) (RValueT b) ~ RValueT c
    , SingI a
    , SingI b
    ) => Arithmetic sup sub ArithmeticTag a 
      -> Arithmetic sup sub ArithmeticTag b 
      -> Arithmetic sup sub ArithmeticTag c 
pattern ArithPowerE a b <- Power 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict
    ) a b 
    where ArithPowerE a b = Power 
            ( Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            , Dict
            ) a b

type instance UMinusX sup sub ArithmeticTag a =
  ( Dict (SingI a)
  , Dict (Biject sup (RValueT a))
  , Dict (Biject sub (RValueT a))
  , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
  , Dict (ArithNumType (RValueT a) ~ ArithNumType (UOpReturn UMinusTag (RValueT a)))
  , Dict (UOp UMinusTag (RValueT a))
  )

pattern ArithUMinusE :: forall sup sub a. 
  ( SingI a
  , Biject sup (RValueT a)
  , Biject sub (RValueT a)
  , TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag))
  , UOp UMinusTag (RValueT a)
  , ArithNumType (UOpReturn UMinusTag (RValueT a)) ~ ArithNumType (RValueT a)
  ) => Arithmetic sup sub ArithmeticTag a 
    -> Arithmetic sup sub ArithmeticTag a
pattern ArithUMinusE a  <- UMinus 
    ( Dict
    , Dict
    , Dict
    , Dict
    , Dict
    , Dict 
    ) a  
    where ArithUMinusE a  = UMinus 
            ( Dict
            , Dict
            , Dict
            , Dict 
            , Dict
            , Dict
            ) a 


type instance ArithExpX sup sub ArithmeticTag a = 
  ( sub a 
  , Dict (SingI a)
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (TypesCaseAnalysis (RValue sub))
  )
pattern ArithExpE :: forall sup sub a . 
  ( SingI a 
  , TypesCaseAnalysis (RValue sup)
  , TypesCaseAnalysis (RValue sub)
  ) => sub a
    -> Arithmetic sup sub ArithmeticTag a
pattern ArithExpE a <- ArithExp (a,Dict,Dict,Dict)
  where ArithExpE a  = ArithExp (a,Dict,Dict,Dict)


type instance ArithInhX sup sub ArithmeticTag a = 
  ( sup a 
  , Dict (SingI a)
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (TypesCaseAnalysis (RValue sub))

  )
pattern ArithInhE :: forall sup sub a . 
  ( SingI a 
  , TypesCaseAnalysis (RValue sup)
  , TypesCaseAnalysis (RValue sub)
  ) => sup a 
    -> Arithmetic sup sub ArithmeticTag a
pattern ArithInhE a <- ArithInh (a,Dict,Dict,Dict)
  where ArithInhE a  = ArithInh (a,Dict,Dict,Dict)


type instance ArithUpcastedX sup sub ArithmeticTag a b =
  ( Dict (UpperBound a b ~ Just b)
  , Dict (SingI a)
  , Dict (SingI b)
  , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
  , Dict (Upcast sup)
  , Dict (Upcast sub)
  , UpcastX sup (RValueT a)
  , UpcastX sub (RValueT a)
  )

instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (Value r) where 

  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  
 
  rvalue (Plus ds a b)  = rvalueBinOp ds a b
  rvalue (Minus ds a b) = rvalueBinOp ds a b
  rvalue (Times ds a b) = rvalueBinOp ds a b
  rvalue (Div ds a b)   = rvalueBinOp ds a b
  rvalue (Mod ds a b)   = rvalueBinOp ds a b
  rvalue (Power ds a b) = rvalueBinOp ds a b
  rvalue (UMinus ds a)  = rvalueUOp ds a
    
  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 


rvalueBinOp :: forall tag sup sub a b c. PointwiseDicts tag sup sub a b c 
  -> Arithmetic sup sub ArithmeticTag a 
  -> Arithmetic sup sub ArithmeticTag b
  -> (AssocCtxMonad ArithmeticTag) (Arithmetic sup sub ArithmeticTag (RValueT c))
rvalueBinOp 
  ( Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  , Dict
  ) a b = case (tcarv @a, tcarv @b, tcarv @c ) of
    (Dict,Dict,Dict) -> (,) <$> rvalue a <*> rvalue b >>= \case 
      (ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithExp @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do
        ea <- project @sub @a' a'
        eb <- project @sub @b' b'
        ec <- (***) @tag @a' @b' ea  eb 
        c' <-  inject @sub @(RValueT c) ec
        withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
      (ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithInh @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
        ea <- project @sub @a' a'
        eb <- project @sup @b' b'
        ec <- (***) @tag @a' @b' ea  eb 
        c' <-  inject @sub @(RValueT c) ec
        withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
      (ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithExp @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
        ea <- project a'
        eb <- project b'
        ec <- (***) @tag @a' @b' ea  eb 
        c' <-  inject  ec
        withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict) 
      (ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict), ArithInh @_ @_ @_ @b' (b',Dict,Dict,Dict)) -> do  
        ea <- project a'
        eb <- project b'
        ec <- (***) @tag @a' @b' ea  eb 
        c' <-  inject  ec
        withSingIRType @c $ pure $ ArithExp (c',Dict,Dict,Dict)
      _ -> error "impossible case"
  where  
    tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
    tcarv = typesCaseAnalysisRV

rvalueUOp :: forall tag sup sub a. 
    ( Dict (SingI a)
    , Dict (Biject sup (RValueT a))
    , Dict (Biject sub (RValueT a))
    , Dict (TypesCaseAnalysis (RValue (Arithmetic sup sub ArithmeticTag)))
    , Dict (ArithNumType (RValueT a) ~ ArithNumType (UOpReturn tag (RValueT a)))
    , Dict (UOp tag (RValueT a))
    ) -> Arithmetic sup sub ArithmeticTag a
      -> (AssocCtxMonad ArithmeticTag) (Arithmetic sup sub ArithmeticTag (RValueT a))
rvalueUOp (Dict,Dict,Dict,Dict,Dict,Dict) a = case tcarv @a of
  Dict -> rvalue a >>= \case 
    ArithExp @_ @_ @_ @a' (a',Dict,Dict,Dict) -> do 
      ea <- project a'
      ec <- unaryOp @tag @a' ea 
      c' <- inject  ec 
      withSingIRType @a $ pure $ ArithExp (c',Dict,Dict,Dict)
    ArithInh @_ @_ @_ @a' (a',Dict,Dict,Dict) -> do 
      ea <- project a'
      ec <- unaryOp @tag @a' ea 
      c' <- inject  ec 
      withSingIRType @a $ pure $ ArithInh (c',Dict,Dict,Dict)
    _ -> error "impossible case"
  where 
    tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
    tcarv = typesCaseAnalysisRV


instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (LazyS r) where 

  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  
  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 

  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue _ = error "impossible case"


instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (Lazy r) where 
  
  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  

  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 


  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV

  rvalue _ = error "impossible case"

instance 
  ( AssocCtxMonad (RVCtx sup) ~ AssocCtxMonad ArithmeticTag
  , AssocCtxMonad (RVCtx sub) ~ AssocCtxMonad ArithmeticTag
  ) => RValue (Arithmetic sup sub ArithmeticTag) (Array r) where 
  
  type RVCtx (Arithmetic sup sub ArithmeticTag) = ArithmeticTag  
  rvalue (Plus ds a b)  = rvalueBinOp ds a b
  rvalue (Minus ds a b) = rvalueBinOp ds a b
  rvalue (Times ds a b) = rvalueBinOp ds a b
  rvalue (Div ds a b)   = rvalueBinOp ds a b
  rvalue (Mod ds a b)   = rvalueBinOp ds a b
  rvalue (Power ds a b) = rvalueBinOp ds a b
  rvalue (UMinus ds a)  = rvalueUOp ds a
  rvalue (ArithExp @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithExpE <$> rvalue a 
  rvalue (ArithInh @_ @_ @_ @a (a,Dict,Dict,Dict)) 
    = withSingIRType @a $ ArithInhE <$> rvalue a 
  rvalue (ArithUpcasted @_ @_ @_ @a @b (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) 
    = rvaluePreservesST @a @b
    $ withSingIRType @a
    $ withSingIRType @b
    $ case (tcarv @a, tcarv @b) of
      (Dict,Dict) -> rvalue a >>= \case 
        (ArithExp (ae,Dict,Dict,Dict)) -> case upcast @sub @(RValueT a) @(RValueT b) sub ae of 
          SameTypeUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithExp (fa,Dict,Dict,Dict)
        (ArithInh (ae,Dict,Dict,Dict)) -> case upcast @sup @(RValueT a) @(RValueT b) sup ae of 
          SameTypeUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          LeftUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          RightUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
          SomethingElseUB fa -> pure $ ArithInh (fa,Dict,Dict,Dict)
        _ -> error "imposible case"
    where  
      tcarv :: forall (x :: Types). (SingI x) => Dict (RValue (Arithmetic sup sub ArithmeticTag) x)
      tcarv = typesCaseAnalysisRV


data Exists f where
  MkExists ::  (forall x. Sing x -> UpcastX f x)  -> Exists f

type instance UpcastX (Arithmetic sup sub ArithmeticTag) a  =
  ( UpcastX sup (RValueT a) 
  , UpcastX sub (RValueT a)
  , UpcastX sup a 
  , UpcastX sub a
  , Dict (Upcast sup)
  , Dict (Upcast sub)
  , Dict (SingI a)
  , Dict (AssocCtxMonad (RVCtx sup) ~ TaggedInterpreter ExprTag)
  , Dict (AssocCtxMonad (RVCtx sub) ~ TaggedInterpreter ExprTag)
  , Dict (Biject sup (Array (RValueT a)))
  , Dict (Biject sub (Array (RValueT a)))
  )



instance Upcast (Arithmetic sup sub ArithmeticTag) where
  upcast :: forall (a :: Types) (b :: Types)  
    . SingI b 
    => UpcastX (Arithmetic sup sub ArithmeticTag) a  
    ->  Arithmetic sup sub ArithmeticTag a  
    -> UpperBoundResults (Arithmetic sup sub ArithmeticTag) a b
  upcast 
    -- (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict,Dict)
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (Plus ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Plus ds l r
            LeftUB _      -> LeftUB  $ Plus ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Plus ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Plus ds l r)
  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (Minus ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Minus ds l r
            LeftUB _      -> LeftUB  $ Minus ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Minus ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Minus ds l r)

  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (Times ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Times ds l r
            LeftUB _      -> LeftUB  $ Times ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Times ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Times ds l r)

  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (Div ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Div ds l r
            LeftUB _      -> LeftUB  $ Div ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Div ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Div ds l r)

  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (Mod ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Mod ds l r
            LeftUB _      -> LeftUB  $ Mod ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Mod ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Mod ds l r)

  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (Power ds l r) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ Power ds l r
            LeftUB _      -> LeftUB  $ Power ds l r
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (Power ds l r)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (Power ds l r)
  upcast 
    (supX,subX,_,_, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (UMinus ds l) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
            NonExistentUB -> NonExistentUB
            SameTypeUB _  -> SameTypeUB $ UMinus ds l
            LeftUB _      -> LeftUB  $ UMinus ds l
            RightUB _     -> RightUB 
              $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) (UMinus ds l)
            SomethingElseUB _     -> case sing @(UpperBound a b) of
              SJust @_ @r _ -> ubIsUb @a @b $ SomethingElseUB 
                $ ArithUpcasted 
                  @sup 
                  @sub 
                  @ArithmeticTag 
                  @a 
                  @r 
                  (Dict,Dict,Dict,Dict,Dict,Dict,supX,subX) 
                  (UMinus ds l)

  upcast 
    (_,_,supX,subX, Dict,Dict,Dict,Dict,Dict,Dict,Dict)

    (ArithExp (a,Dict,Dict,Dict)) = case upcast @_ @a @b subX a of
      NonExistentUB      -> NonExistentUB
      SameTypeUB a'      -> SameTypeUB $ ArithExp (a',Dict,Dict,Dict)
      LeftUB a'          -> LeftUB  $ ArithExp (a',Dict,Dict,Dict)
      RightUB a'         -> RightUB $ ArithExp (a',Dict,Dict,Dict)
      SomethingElseUB a' -> SomethingElseUB $ ArithExp (a',Dict,Dict,Dict)

  upcast 
    (_,_,supX,subX, Dict,Dict,Dict,Dict,Dict,Dict,Dict)
    (ArithInh (a,Dict,Dict,Dict)) = case upcast @_ @a @b supX a of
      NonExistentUB      -> NonExistentUB
      SameTypeUB a'      -> SameTypeUB $ ArithInh (a',Dict,Dict,Dict)
      LeftUB a'          -> LeftUB  $ ArithInh (a',Dict,Dict,Dict)
      RightUB a'         -> RightUB $ ArithInh (a',Dict,Dict,Dict)
      SomethingElseUB a' -> SomethingElseUB $ ArithInh (a',Dict,Dict,Dict)

  upcast 
    (f,g,supX,subX, Dict,Dict,Dict,Dict,Dict,Dict,Dict)
    (ArithUpcasted @_ @_ @_ @x (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a) = case upcastable @a @b @Arithmetic @sup @sub @ArithmeticTag of
      NonExistentUB     -> NonExistentUB
      SameTypeUB _      -> SameTypeUB $ ArithUpcasted (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a
      LeftUB _          -> LeftUB  $ ArithUpcasted  (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a
      RightUB _         
        -> ubIsTransitive' @x @a @b 
        $ RightUB 
        $ ArithUpcasted @_ @_ @_ @x (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a
      SomethingElseUB _ 
        -> withSingIUBType @a @b $ case sing @(UpperBound a b) of
          SJust @_ @r sr 
            -> withSingI sr 
            $ ubIsTransitive' @x @a @b -- x ^ b ~ r
            $ ubIsIdempotent @r        -- r ^ r ~ r
            $ ubIsUb @x @b
            $ SomethingElseUB 
            $ ArithUpcasted @_ @_ @_ @x (Dict,Dict,Dict,Dict,Dict,Dict,sup,sub) a

instance 
  ( Monad m
  , C (ShowM m) sup
  , C (ShowM m) sub
  ) => ShowM m (Arithmetic sup sub ArithmeticTag a) where 
  showsPrecM p = \case 
    Plus  _ l r -> showParenM (p > 6) $ showsPrecM 6 l <=< showStringM " + " <=< showsPrecM 7 r
    Minus _ l r -> showParenM (p > 6) $ showsPrecM 6 l <=< showStringM " - " <=< showsPrecM 7 r
    Times _ l r -> showParenM (p > 7) $ showsPrecM 7 l <=< showStringM " * " <=< showsPrecM 8 r
    Div   _ l r -> showParenM (p > 7) $ showsPrecM 7 l <=< showStringM " / " <=< showsPrecM 8 r
    Mod   _ l r -> showParenM (p > 7) $ showsPrecM 7 l <=< showStringM " % " <=< showsPrecM 8 r
    Power _ l r -> showParenM (p > 8) $ showsPrecM 9 l <=< showStringM " ^ " <=< showsPrecM 8 r
    UMinus _ l  -> showStringM "-" <=< showsPrecM 9 l
    ArithExp (a,_,_,_) -> showsPrecM p a 
    ArithInh (a,_,_,_) -> showsPrecM p a
    ArithUpcasted _ a -> showsPrecM p a


