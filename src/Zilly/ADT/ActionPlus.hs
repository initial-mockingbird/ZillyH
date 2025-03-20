{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Zilly.ADT.Expression
Description : Main Action  Tree for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

TODO: adapt it to fit trees that grow.

-}
module Zilly.ADT.ActionPlus where

import Utilities.LensM
import Zilly.ADT.ExpressionPlus
import Zilly.Types
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter
import Zilly.ZillyPlus.Tower
import Zilly.ZillyPlus.Expression
import Utilities.TypedMapPlus
import Utilities.ShowM
import Data.Proof 
import Control.Monad.Reader

import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad
import Data.Singletons (SingI)
import Debug.Trace (trace)
import Control.Applicative (Alternative)
import Data.Singletons (SingI(..))
import Data.Sequence
import InequalityFamily 

type family AssocActionTag (ctx :: Type) :: Type

infix 0 :=
infix 0 :=.
data A ctx where
  (:=) :: forall ctx  (e :: Types) (a :: Types).
    AssignX ctx e a -> LensM (AssocCtxMonad ctx) (E Void2 ErrorT ExprTag a) -> ET e -> A ctx
  (:=.) :: forall ctx  (e :: Types) (a :: Types).
    ReAssignX ctx e a -> LensM (AssocCtxMonad ctx) (E Void2 ErrorT ExprTag a) -> ET e -> A ctx
  Print :: forall ctx a.
    PrintX ctx a -> ET a -> A ctx 

type family AssignX   (ctx :: Type) (e :: Types) (a :: Types) :: Type 
type family ReAssignX (ctx :: Type) (e :: Types) (a :: Types) :: Type 
type family PrintX    (ctx :: Type) (a :: Types) :: Type


type instance AssocCtxMonad ActionTag = TaggedInterpreter ExprTag
type instance Gamma (TaggedInterpreter ActionTag) = TypeRepMap ErrorT ExprTag


type instance AssignX ActionTag e var = 
  ( Dict (UpperBound (RValueT var) (RValueT e) ~ Just (RValueT var))
  , Dict (AssocCtxMonad ActionTag ~ AssocCtxMonad ExprTag)
  , Dict (AssocCtxMonad ExprTag ~ TaggedInterpreter ExprTag)
  , Dict (SingI e)
  , Dict (SingI var)
  )
pattern AssignE :: forall . forall e var. 
  ( UpperBound (RValueT var) (RValueT e) ~ Just (RValueT var)
  , AssocCtxMonad ActionTag ~ AssocCtxMonad ExprTag 
  , AssocCtxMonad ExprTag ~ TaggedInterpreter ExprTag 
  , SingI e
  , SingI var 
  ) => LensM (AssocCtxMonad ActionTag) (E Void2 ErrorT ExprTag var) ->ET e -> A ActionTag 
pattern AssignE l r <- (:=) (Dict,Dict,Dict,Dict,Dict) l r 
  where AssignE l r  = (:=) (Dict,Dict,Dict,Dict,Dict) l r

type instance ReAssignX ActionTag e var = 
  ( Dict (UpperBound (RValueT var) (RValueT e) ~ Just (RValueT var))
  , Dict (AssocCtxMonad ActionTag ~ AssocCtxMonad ExprTag)
  , Dict (AssocCtxMonad ExprTag ~ TaggedInterpreter ExprTag)
  , Dict (SingI e)
  , Dict (SingI var)
  )
pattern ReassignE :: forall . forall e var. 
  ( UpperBound (RValueT var) (RValueT e) ~ Just (RValueT var)
  , AssocCtxMonad ActionTag ~ AssocCtxMonad ExprTag 
  , AssocCtxMonad ExprTag ~ TaggedInterpreter ExprTag 
  , SingI e
  , SingI var 
  ) => LensM (AssocCtxMonad ActionTag) (E Void2 ErrorT ExprTag var) ->ET e -> A ActionTag 
pattern ReassignE l r <- (:=.) (Dict,Dict,Dict,Dict,Dict) l r 
  where ReassignE l r  = (:=.) (Dict,Dict,Dict,Dict,Dict) l r


type instance PrintX ActionTag e = 
  ( Dict (AssocCtxMonad ActionTag ~ AssocCtxMonad ExprTag)
  , Dict (AssocCtxMonad ExprTag ~ TaggedInterpreter ExprTag)
  , Dict (SingI e)
  )
pattern PrintE :: forall . forall e. 
  ( AssocCtxMonad ActionTag ~ AssocCtxMonad ExprTag 
  , AssocCtxMonad ExprTag ~ TaggedInterpreter ExprTag 
  , SingI e
  ) => ET e -> A ActionTag 
pattern PrintE l  <- Print (Dict,Dict,Dict) l  
  where PrintE l   = Print (Dict,Dict,Dict) l 


data ActionTag

class Execute ctx where
  execInstruction :: forall  {m} {env}. 
    ( AssocCtxMonad ctx ~ m
    , Gamma m ~ env
    ) => A ctx -> m (A ctx, env)




instance Execute ActionTag where 
  execInstruction  
    ( (:=) 
      @ActionTag 
      @e 
      @var 
      (Dict,Dict,Dict,Dict,Dict) 
      var
      e'@(ETower e) 
    )
      = withSingIRType @var
      $ withSingIRType @e
      $ ubIsCommutative @(RValueT var) @(RValueT e)
      $ do
        gamma  <- declare @(RValueT var) @ExprTag (varNameM var) =<< ask
        (ETower rve) <- local (const gamma) $ case sing @e of 
          SValue _ -> rvalue e'
          SLazy _  -> rvalue e' 
          SLazyS _ -> rvalue e' 
          SArray _ -> rvalue e'
      
        let upcastE = case sing @(RValueT e) of 
              SValue _ -> UpcastE 
              SLazy _  -> UpcastE 
              SLazyS _ -> UpcastE 
              SArray _ -> UpcastE 

        gamma' <- case upcast @_ @(RValueT e) @(RValueT  var) upcastE rve of
          SameTypeUB  rve'     -> insert @(RValueT var) @ExprTag (varNameM var) rve' gamma
          RightUB     rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
          LeftUB      rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
          SomethingElseUB rve' -> insert @(RValueT var) (varNameM var) rve' gamma
        pure ((:=) (Dict,Dict,Dict,Dict,Dict) var (ETower e),gamma')
  execInstruction  
   ( (:=.)
      @ActionTag 
      @e 
      @var 
      (Dict,Dict,Dict,Dict,Dict) 
      var
      e'@(ETower e) 
   )
      = withSingIRType @var
      $ withSingIRType @e
      $ ubIsCommutative @(RValueT var) @(RValueT e)
      $ do
        gamma  <- ask
        (ETower rve) <-  case sing @e of 
          SValue _ -> rvalue e'
          SLazy _  -> rvalue e' 
          SLazyS _ -> rvalue e' 
          SArray _ -> rvalue e'
      
        let upcastE = case sing @(RValueT e) of 
              SValue _ -> UpcastE 
              SLazy _  -> UpcastE 
              SLazyS _ -> UpcastE 
              SArray _ -> UpcastE 

        gamma' <- case upcast @_ @(RValueT e) @(RValueT  var) upcastE rve of
          SameTypeUB  rve'     -> insert @(RValueT var) @ExprTag (varNameM var) rve' gamma
          RightUB     rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
          LeftUB      rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
          SomethingElseUB rve' -> insert @(RValueT var) (varNameM var) rve' gamma
        pure ((:=.) (Dict,Dict,Dict,Dict,Dict) var (ETower e),gamma')
  execInstruction (Print @ActionTag @e (Dict,Dict,Dict)  e) 
    = withSingIRType @e 
    $ do
    gamma <- ask
    rve <- case sing @e of 
      SValue _ -> Print (Dict,Dict,Dict) <$> rvalue @ET @e e
      SLazy _  -> Print (Dict,Dict,Dict) <$> rvalue @ET @e e
      SLazyS _ -> Print (Dict,Dict,Dict) <$> rvalue @ET @e e
      SArray _ -> Print (Dict,Dict,Dict) <$> rvalue @ET @e e
    pure (rve, gamma )


