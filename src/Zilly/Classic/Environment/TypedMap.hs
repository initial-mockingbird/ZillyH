{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module Zilly.Classic.Environment.TypedMap where


import Data.Map (Map)
import qualified Data.Map as M

import Type.Reflection 
import Zilly.Classic.Newtypes

import Debug.Trace
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Data.Singletons
import Data.String (IsString(..))
import Data.Singletons.Decide 
import Data.Kind (Type)


-------------------------------
-- Errors
--------------------------------

data ExpectedType = ExpectedType String 
data ActualType = ActualType String

data GammaErrors
  =  TypeMismatch String ExpectedType ActualType 
  |  VariableNotDefined String
  |  VariableAlreadyDeclared String
  |  VariableNotInitialized String

--------------------------------
-- Lens interface
--------------------------------

type family EvalMonad (f :: PTypes -> Type) :: Type -> Type

-- Defines a way to get, set, set fresh and obtain the name of a variable
data LensM (f :: PTypes -> Type) (ltype :: PTypes) = LensM
  { getL  ::  TypeRepMap f -> (EvalMonad f) (Either GammaErrors (f (Ftype ltype)))
  , setL  ::  TypeRepMap f -> f (Ftype ltype) -> (EvalMonad f) (Either GammaErrors (TypeRepMap f))
  , setFL ::  TypeRepMap f -> f (Ftype ltype) ->  (EvalMonad f)(Either GammaErrors (TypeRepMap f))
  , varNameM :: String
  }

viewM ::LensM f ltype -> TypeRepMap f -> (EvalMonad f)(Either GammaErrors (f (Ftype ltype)))
viewM  = getL

setM :: LensM f ltype -> f (Ftype ltype) -> TypeRepMap f -> (EvalMonad f) (Either GammaErrors (TypeRepMap f))
setM = flip . setL

setMF :: LensM f ltype -> f (Ftype ltype) -> TypeRepMap f -> (EvalMonad f) (Either GammaErrors (TypeRepMap f))
setMF = flip . setFL



data Any (f :: PTypes -> Type)  where
  MkAny :: forall (a :: PTypes) f.  SingI a => MVar (f a) -> Any f 

newtype TypeRepMap f = TypeRepMap (Map String (Any f))

empty :: TypeRepMap f
empty = TypeRepMap M.empty 

scope :: TypeRepMap f -> [String]
scope (TypeRepMap m) = M.keys m 

isInScope :: String -> TypeRepMap ctx -> Bool 
isInScope s (TypeRepMap m) = s `M.member` m 



insert :: forall a f m.  
  ( SingI a
  , MonadIO m

  ) => String -> f a -> TypeRepMap f -> m (Either GammaErrors (TypeRepMap f))
insert var val (TypeRepMap m) = case M.lookup var m of
  Just (MkAny @a' @_ mv ) -> case decideEquality (sing @a') (sing @a) of 
    Just Refl -> do
      liftIO $ tryTakeMVar mv >> putMVar mv val
      pure . pure . TypeRepMap $ m
    Nothing -> pure . Left $ TypeMismatch var 
      (ExpectedType $ withShow @a')
      (ActualType $ withShow @a)
  Nothing -> do
    mv  <- liftIO $ newMVar val
    pure . pure . TypeRepMap $ M.insert var (MkAny @a mv) m

reassignWith :: forall a f m.  
  ( SingI a
  , MonadIO m
  ) => String -> (f a -> f a) -> TypeRepMap f -> m (Either GammaErrors (TypeRepMap f))
reassignWith var f (TypeRepMap m) = case M.lookup var m of
  Just (MkAny @a' @_ mv ) -> case decideEquality (sing @a') (sing @a) of 
    Just Refl -> do
      liftIO $ takeMVar mv >>= putMVar mv . f
      pure . pure . TypeRepMap $ m
    Nothing -> pure . Left $ TypeMismatch var 
      (ExpectedType $ withShow @a')
      (ActualType $ withShow @a)
 
  Nothing -> pure . Left $ VariableNotDefined var

insertFresh :: forall a f m. 
  ( SingI a
  , MonadIO m
  ) => String -> f a -> TypeRepMap f -> m (Either GammaErrors (TypeRepMap f ))
insertFresh var val (TypeRepMap m) = do
    mv <- liftIO $ newMVar val
    pure . pure . TypeRepMap $ M.insert var (MkAny mv) m

declare :: forall (a :: PTypes) f m. 
  ( SingI a
  , MonadIO m
  ) =>  String -> TypeRepMap f -> m (Either GammaErrors (TypeRepMap f))
declare  var (TypeRepMap m) = case M.lookup var m of
  Just _ -> pure . Left $ VariableAlreadyDeclared var
  Nothing -> do
    mv <- liftIO $ newEmptyMVar @(f a)
    !x <- pure . pure . TypeRepMap $ M.insert var (MkAny mv) m
    pure x


yield :: forall (a :: PTypes) f m. 
  ( SingI a
  ,  MonadIO m
  ) => String -> TypeRepMap f  -> m (Either GammaErrors (f a))
yield var (TypeRepMap m) = 
  case M.lookup var m of
    Just (MkAny @a' mv ) -> case decideEquality (sing @a') (sing @a)  of
      Just Refl -> liftIO (tryReadMVar mv) >>= \case 
        Nothing -> (error $ "Var " <> show var <> " not inizialited" ) 
        Just e -> pure $ Right e
      Nothing ->  pure . Left $ TypeMismatch var 
        (ExpectedType $ withShow @a')
        (ActualType $ withShow @a)    
    Nothing ->  pure . Left $ VariableNotDefined var


instance forall  (ltype :: PTypes) f. 
  ( SingI ltype
  , MonadIO (EvalMonad f)
  ) => IsString (LensM f ltype) where
  fromString var = withSingIFtype @ltype $ LensM 
    (yield @(Ftype ltype) var) 
    (flip $ insert var) 
    (flip $ insertFresh var) var


mkVar :: forall  (ltype :: PTypes) f. 
  ( SingI ltype 
  , MonadIO (EvalMonad f)
  ) => String -> LensM f ltype
mkVar = fromString


