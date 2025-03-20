{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ImpredicativeTypes         #-}
--{-# LANGUAGE TypeAbstractions #-}

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
module Zilly.ZillyPlus.Comparison where

import Utilities.LensM
import Utilities.TypedMap
import Zilly.Types
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Arithmetic
import Zilly.ADT.Comparison
import Zilly.ADT.Array
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter
import Zilly.ZillyPlus.Expression

import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Typeable hiding (cast)
import Control.Monad.Reader 
import Control.Monad

import Control.Applicative
import Prelude.Singletons (SingI,SMaybe(..),sing,withSingI)

import Data.Singletons.Decide
import Data.Function.Singletons
import Debug.Trace (trace)
import Utilities.ShowM
import Prelude hiding (LT,GT,EQ)
import Data.Maybe.Singletons (IsJust,FromJust)

--
-- type family Comparable (a :: Types) :: Maybe Type where
--   Comparable (Value Z) = (Just Int)
--   Comparable (Value F) = (Just Float)
--   Comparable _         = Nothing
--
-- type instance MinusX f ExprTag a b c = 
--   ( Dict ((RValue E Void2 ExprTag) a)
--   , Dict ((RValue E Void2 ExprTag) b)
--   , Dict ( UpperBound a b ~ Just c )
--   , Dict (Numeric c ~ True)
--   )
-- pattern MinusE :: () =>
--   ( RValue E Void2 ExprTag a
--   , RValue E Void2 ExprTag b
--   , UpperBound a b ~ Just c
--   , Numeric c ~ True
--   ) 
--   => f ExprTag a -> f ExprTag b -> Arithmetic f ExprTag c
-- pattern MinusE a b <- Minus (Dict,Dict,Dict,Dict) a b
--   where MinusE a b = Minus (Dict,Dict,Dict,Dict) a b
--
-- type instance LTX f ExprTag a b c =
--   ( Dict (RValue E Void2 ExprTag a)
--   , Dict (a ~ b)
--   , Dict (a ~ c)
--   , Dict (IsJust(Comparable c) ~ True)
--   , Dict (SingI a)
--   )
-- pattern LTE :: () =>
--   ( RValue E Void2 ExprTag a
--   , a ~ b
--   , a ~ c
--   , IsJust (Comparable c) ~ True
--   , SingI a
--   ) 
--   => f ExprTag a -> f ExprTag b -> Comparison f ExprTag c
-- pattern LTE a b <- LT (Dict,Dict,Dict,Dict,Dict) a b
--   where LTE a b = LT (Dict,Dict,Dict,Dict,Dict) a b
--
-- type instance LTEQX f ExprTag a b c = LTX f ExprTag a b c
-- type instance GTX   f ExprTag a b c = LTX f ExprTag a b c
-- type instance GTEQX f ExprTag a b c = LTX f ExprTag a b c
-- type instance EQX   f ExprTag a b c = LTX f ExprTag a b c
-- type instance NEQX  f ExprTag a b c = LTX f ExprTag a b c
--
-- type instance ComparisonInhX (E Void2) ExprTag a = 
--   Dict (SingI a)
--
-- instance 
--   ( MonadIO (AssocCtxMonad ExprTag)
--   , Alternative (AssocCtxMonad ExprTag)
--   , MonadReader (Gamma (AssocCtxMonad ExprTag)) (AssocCtxMonad ExprTag)
--   , BasicValue (Value a) ~ Just a'
--   , Show a'
--   ) => RValue Comparison (E Void2) ExprTag (Value a) where
--
--   rvalue (LT  (Dict,Dict,Dict,_,Dict) a b) = case sing @(Value a) of
--     SValue SZ -> comparisonAux a b LTE (<) rConnector
--     SValue SF -> comparisonAux a b LTE (<) rConnector
--     
--   rvalue (LTEQ  (Dict,Dict,Dict,_,Dict) a b) = case sing @(Value a) of
--     SValue SZ -> comparisonAux a b LTE (<) rConnector
--     SValue SF -> comparisonAux a b LTE (<) rConnector
--
--   rvalue (GT  (Dict,Dict,Dict,_,Dict) a b) = case sing @(Value a) of
--     SValue SZ -> comparisonAux a b LTE (<) rConnector
--     SValue SF -> comparisonAux a b LTE (<) rConnector
--
--   rvalue (GTEQ  (Dict,Dict,Dict,_,Dict) a b) = case sing @(Value a) of
--     SValue SZ -> comparisonAux a b LTE (<) rConnector
--     SValue SF -> comparisonAux a b LTE (<) rConnector
--
--   rvalue (EQ  (Dict,Dict,Dict,_,Dict) a b) = case sing @(Value a) of
--     SValue SZ -> comparisonAux a b LTE (<) rConnector
--     SValue SF -> comparisonAux a b LTE (<) rConnector
--
--   rvalue (NEQ  (Dict,Dict,Dict,_,Dict) a b) = case sing @(Value a) of
--     SValue SZ -> comparisonAux a b LTE (<) rConnector
--     SValue SF -> comparisonAux a b LTE (<) rConnector
--
--   -- rvalue (ComparisonInh Dict f) = case sing @(Value a) of
--   --   SValue SZ -> ComparisonInh Dict <$> rvalue f 
--   --   SValue SF -> ComparisonInh Dict <$> rvalue f
--   rvalue _ = undefined
--
-- instance (BasicValue x ~ Just x', Show x') => Show (Comparison (E Void2) ExprTag x)
--
-- comparisonAux :: forall {a'} (a :: Types0).
--   ( Comparable (Value a) ~ Just a'
--   , SingI (Value a)
--   , BasicValue (Value a) ~ Just a'
--   , Show a'
--   , RValue E Void2 ExprTag (Value a)
--   ) => E Void2 ExprTag (Value a) 
--     -> E Void2 ExprTag (Value a) 
--     -> (forall (b :: Types). 
--       ( IsJust (Comparable b) ~ True
--       , RValue E Void2 ExprTag b
--       , SingI b
--       ) => E Void2 ExprTag b -> E Void2 ExprTag b -> Comparison (E Void2)  ExprTag b)
--     -> (a' -> a' -> Bool)
--     -> (Bool -> a')
--     -> (AssocCtxMonad ExprTag) (Comparison (E Void2)  ExprTag (Value a))
-- comparisonAux a b inj comp rConnector = (,) <$> rvalue a <*> rvalue b >>= \case
--       (ValE a', ValE b') -> pure . ComparisonInh Dict . ValE . rConnector $ comp a' b'
--       (a',b') -> liftA2 inj (rvalue a') (rvalue b') >>=  rvalue
--   
--
