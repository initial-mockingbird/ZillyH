{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
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
{-# LANGUAGE LambdaCase                 #-}

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
module Zilly.ZillyPlus.Error where

import Data.Proof
import Utilities.LensM
import Utilities.TypedMapPlus
import Zilly.Types
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.Error
import Zilly.RValuePlus
import Zilly.UpcastPlus
import Zilly.ZillyPlus.Interpreter
import Zilly.ZillyPlus.Expression
import Utilities.ShowM

import Control.Applicative
import Prelude.Singletons (SingI,SMaybe(..),sing)

import Data.Singletons.Decide
import Prelude hiding (LT,GT,EQ)

data ErrorTag


type instance AssocCtxMonad ErrorTag = TaggedInterpreter ExprTag


type instance ErrorLiteralX sup sub ErrorTag a = Void

type instance ErrorInhX sup sub ErrorTag a = 
  ( sup a 
  , Dict (TypesCaseAnalysis (RValue sup))
  , Dict (AssocCtxMonad ErrorTag ~ AssocCtxMonad (RVCtx sup))
  )
pattern ErrorInhE :: forall sup sub a. 
  ( TypesCaseAnalysis (RValue sup)
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sup)
  ) => sup a -> Error sup sub ErrorTag a
pattern ErrorInhE x0  <- ErrorInh (x0,Dict,Dict)
  where ErrorInhE x0   = ErrorInh (x0,Dict,Dict)


type instance ErrorExpX sup sub ErrorTag a = 
  ( sub a 
  , Dict (TypesCaseAnalysis (RValue sub))
  , Dict (AssocCtxMonad ErrorTag ~ AssocCtxMonad (RVCtx sub))
  )
pattern ErrorExpE :: forall sup sub a. 
  ( TypesCaseAnalysis (RValue sub)
  , AssocCtxMonad ExprTag ~ AssocCtxMonad (RVCtx sub)
  ) => sub a -> Error sup sub ErrorTag a
pattern ErrorExpE x0  <- ErrorExp (x0,Dict,Dict)
  where ErrorExpE x0   = ErrorExp (x0,Dict,Dict)

instance RValue (Error sup sub ErrorTag) (Value a) where
  type RVCtx (Error sup sub ErrorTag) = ErrorTag  
  rvalue (ErrorLiteral v msg) = pure $ ErrorLiteral v msg
  rvalue (ErrorExp (v,Dict,Dict)) = ErrorExpE <$> rvalue v
  rvalue (ErrorInh (v,Dict,Dict)) = ErrorInhE <$> rvalue v

instance RValue (Error sup sub ErrorTag) (Lazy a) where
  type RVCtx (Error sup sub ErrorTag) = ErrorTag  
  rvalue (ErrorLiteral v msg) = pure $ ErrorLiteral v msg
  rvalue (ErrorExp (v,Dict,Dict)) = ErrorExpE <$> rvalue v
  rvalue (ErrorInh (v,Dict,Dict)) = ErrorInhE <$> rvalue v

instance RValue (Error sup sub ErrorTag) (LazyS a) where
  type RVCtx (Error sup sub ErrorTag) = ErrorTag  
  rvalue (ErrorLiteral v msg) = pure $ ErrorLiteral v msg
  rvalue (ErrorExp (v,Dict,Dict)) = ErrorExpE <$> rvalue v
  rvalue (ErrorInh (v,Dict,Dict)) = ErrorInhE <$> rvalue v

instance RValue (Error sup sub ErrorTag) (Zilly.Types.Array a) where
  type RVCtx (Error sup sub ErrorTag) = ErrorTag  
  rvalue (ErrorLiteral v msg) = pure $ ErrorLiteral v msg
  rvalue (ErrorExp (v,Dict,Dict)) = ErrorExpE <$> rvalue v
  rvalue (ErrorInh (v,Dict,Dict)) = ErrorInhE <$> rvalue v

type instance UpcastX (Error sup sub ErrorTag) a  =
  ( UpcastX sup a  
  , UpcastX sub a 
  , Dict (Upcast sup)
  , Dict (Upcast sub)
  , Dict (SingI a)
  -- , Dict (TypesCaseAnalysis (RValue (Error sup sub ErrorTag)))
  -- , Dict (TypesCaseAnalysis (RValue sup))
  -- , Dict (TypesCaseAnalysis (RValue sub))
  )
pattern UpcastErrorE :: forall sup sub a . 
  ( Upcast sup 
  , Upcast sub
  , SingI a
  , TypesCaseAnalysis (RValue (Error sup sub ErrorTag))
  , TypesCaseAnalysis (RValue sup)
  , TypesCaseAnalysis (RValue sub)
  ) => UpcastX sup a  -> UpcastX sub a  -> UpcastX (Error sup sub ErrorTag) a  
pattern UpcastErrorE sup sub <- (sup,sub,Dict,Dict,Dict) -- (sup,sub,Dict,Dict,Dict,Dict,Dict,Dict)
  where UpcastErrorE sup sub  = (sup,sub,Dict,Dict,Dict)

instance Upcast (Error sup sub ErrorTag) where
  upcast :: forall (a :: Types) (b :: Types)  
    . SingI b 
    => UpcastX (Error sup sub ErrorTag) a  
    ->  Error sup sub ErrorTag a  
    -> UpperBoundResults (Error sup sub ErrorTag) a b
  -- upcast (_,_,Dict,Dict,Dict,Dict,Dict,Dict) (ErrorLiteral v msg) 
  upcast (_,_,Dict,Dict,Dict) (ErrorLiteral v msg) 

    = withRVType @(Error sup sub ErrorTag) (sing @a)
    $ withRVType @(Error sup sub ErrorTag) (sing @b)
    $ case upcastable @a @b @Error @sup @sub @ErrorTag of
      NonExistentUB -> NonExistentUB
      SameTypeUB      _ -> SameTypeUB (ErrorLiteral v msg)
      LeftUB          _ -> LeftUB (ErrorLiteral v msg)
      RightUB         _ -> RightUB (ErrorLiteral v msg)
      SomethingElseUB _ -> SomethingElseUB (ErrorLiteral v msg)
  -- upcast (supX,_,Dict,Dict,Dict,Dict,Dict,Dict) (ErrorInh (v,Dict,Dict))
  upcast (supX,_,Dict,Dict,Dict) (ErrorInh (v,Dict,Dict))

    = withRVType @sup (sing @b)
    $ case upcast @sup @a @b supX v of
      NonExistentUB        -> NonExistentUB
      SameTypeUB      supA -> SameTypeUB (ErrorInh (supA,Dict,Dict))
      LeftUB          supA -> LeftUB (ErrorInh (supA,Dict,Dict))
      RightUB         supA -> RightUB (ErrorInh (supA,Dict,Dict))
      SomethingElseUB supA -> case sing @(UpperBound a b) of
        SJust (SValue _) -> SomethingElseUB (ErrorInh (supA,Dict,Dict))
        SJust (SLazy _) -> SomethingElseUB (ErrorInh (supA,Dict,Dict))
        SJust (SLazyS _) -> SomethingElseUB (ErrorInh (supA,Dict,Dict))
        SJust (SArray _) -> SomethingElseUB (ErrorInh (supA,Dict,Dict))

  -- upcast (_,subX,Dict,Dict,Dict,Dict,Dict,Dict) (ErrorExp (v,Dict,Dict))
  upcast (_,subX,Dict,Dict,Dict) (ErrorExp (v,Dict,Dict))

    = withRVType @sub (sing @b)
    $ case upcast @sub @a @b subX v of
      NonExistentUB        -> NonExistentUB
      SameTypeUB      supA -> SameTypeUB (ErrorExp (supA,Dict,Dict))
      LeftUB          supA -> LeftUB (ErrorExp (supA,Dict,Dict))
      RightUB         supA -> RightUB (ErrorExp (supA,Dict,Dict))
      SomethingElseUB supA -> case sing @(UpperBound a b) of
        SJust (SValue _) -> SomethingElseUB (ErrorExp (supA,Dict,Dict))
        SJust (SLazy _) -> SomethingElseUB (ErrorExp (supA,Dict,Dict))
        SJust (SLazyS _) -> SomethingElseUB (ErrorExp (supA,Dict,Dict))
        SJust (SArray _) -> SomethingElseUB (ErrorExp (supA,Dict,Dict))


instance 
  ( Monad m
  , C (ShowM m) sup
  , C (ShowM m) sub
  ) => ShowM m (Error sup sub ErrorTag a) where 
  showsPrecM p = \case 
    (ErrorLiteral _ s) ->  showStringM s 
    (ErrorExp (a,_,_)) -> showsPrecM p a
    (ErrorInh (a,_,_)) -> showsPrecM p a

