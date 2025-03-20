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
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeOperators #-}
module Utilities.TypedMapPlus where


import Data.Map (Map)
import qualified Data.Map as M

import Unsafe.Coerce
import Type.Reflection 
--import Control.Lens.Lens
import Utilities.LensM
import Utilities.ShowM
import Zilly.ADT.ExpressionPlus
import Zilly.Types
import Data.Proof

import Debug.Trace
import Data.List.NonEmpty ( NonEmpty((:|)) )
import Data.Foldable1 (foldl1')
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Control.Monad
import Control.Applicative hiding (yield)
import Data.Singletons
import Data.String (IsString(..))
import Data.Singletons.Decide 
import Control.Monad.Reader
import Data.Kind (Type)


data Any sub ctx where
  MkAny :: forall (a :: Types) ctx sub.  SingI a => MVar (E Void2 sub ctx a) -> Any sub ctx 

newtype TypeRepMap sub ctx = TypeRepMap (Map Symbol (Any sub ctx))

empty :: TypeRepMap sub ctx
empty = TypeRepMap M.empty 

inScope :: TypeRepMap sub ctx -> [Symbol]
inScope (TypeRepMap m) = M.keys m 

insert :: forall {m} a ctx sub.  
  ( SingI a
  , AssocCtxMonad ctx ~ m
  , MonadIO m
  ) => Symbol -> E Void2 sub ctx a -> TypeRepMap sub ctx -> m (TypeRepMap sub ctx)
insert var val (TypeRepMap m) = case M.lookup var m of
  Just (MkAny @a' @_ mv ) -> case decideEquality (sing @a') (sing @a) of 
    Just Refl -> do
      liftIO $ tryTakeMVar mv >> putMVar mv val
      pure . TypeRepMap $ m
    Nothing -> error 
      $ "Type mismatch for variable: " 
      <> show var <> ", expected: " 
      <> show (fromSing $ sing @a) 
      <> " got: " 
      <> show (fromSing $ sing @a') 
  Nothing -> do
    mv  <- liftIO $ newMVar val
    pure . TypeRepMap $ M.insert var (MkAny @a mv) m

reassignWith :: forall {m} a ctx sub.  
  ( SingI a
  , AssocCtxMonad ctx ~ m
  , MonadIO m
  ) => Symbol -> (E Void2 sub ctx a -> E Void2 sub ctx a) -> TypeRepMap sub ctx -> m (TypeRepMap sub ctx)
reassignWith var f (TypeRepMap m) = case M.lookup var m of
  Just (MkAny @a' @_ mv ) -> case decideEquality (sing @a') (sing @a) of 
    Just Refl -> do
      liftIO $ takeMVar mv >>= putMVar mv . f
      pure . TypeRepMap $ m
    Nothing -> error 
      $ "Type mismatch for variable: " 
      <> show var <> ", expected: " 
      <> show (fromSing $ sing @a) 
      <> " got: " 
      <> show (fromSing $ sing @a') 
  Nothing -> error  
    $ "Variable: "
    <> show var 
    <> " not defined"



insertFresh :: forall {m} a ctx sub. 
  ( SingI a
  , AssocCtxMonad ctx ~ m
  , MonadIO m
  ) => Symbol -> E Void2 sub ctx a -> TypeRepMap sub ctx -> m (TypeRepMap sub ctx )
insertFresh var val (TypeRepMap m) = do
    mv <- liftIO $ newMVar val
    pure . TypeRepMap $ M.insert var (MkAny mv) m

declare :: forall {m} (a :: Types) ctx sub. 
  ( SingI a
  , MonadIO m
  , AssocCtxMonad ctx ~ m
  ) =>  Symbol -> TypeRepMap sub ctx -> m (TypeRepMap sub ctx)
declare  var (TypeRepMap m) = case M.lookup var m of
  Just _ -> error $ "Variable: " <> show var <> " already declared"
  Nothing -> do
    mv :: MVar (E Void2 sub ctx a) <- liftIO newEmptyMVar 
    !x <- pure . TypeRepMap $ M.insert var (MkAny mv) m

    pure x


yield :: forall {m} (a :: Types) ctx sub. 
  ( SingI a
  , AssocCtxMonad ctx ~ m
  ,  MonadIO m
  ) => Symbol -> TypeRepMap sub ctx  -> m (E Void2 sub ctx a)
yield var (TypeRepMap m) = 
  case M.lookup var m of
    Just (MkAny @a' mv ) -> case decideEquality (sing @a') (sing @a)  of
      Just Refl -> unsafeCoerce . maybe (error $ "Var " <> show var <> " not inizialited" ) id <$> liftIO (tryReadMVar  mv )
      Nothing -> error 
        $ "Type mismatch for symbol: " 
        <> show var <> ", expected: " 
        <> show (fromSing $ sing @a) 
        <> " got: " 
        <> show (fromSing $ sing @a') 
    Nothing -> error $ "Variable: " <> show var <> " not found"


instance forall  (a :: Types) (ctx :: Type) (sub :: Types -> Type) m. 
  ( SingI a
  , AssocCtxMonad ctx ~ m
  , MonadIO m
  , Gamma m ~ TypeRepMap sub ctx 
  ) => IsString (LensM m (E Void2 sub ctx a)) where
  fromString var =  LensM (yield var) (flip $ insert var) (flip $ insertFresh var) var 

mkVar :: forall {m :: Type -> Type} (a :: Types) ctx sub. 
  ( SingI a
  , AssocCtxMonad ctx ~ m
  , MonadIO m
  , Gamma m ~ TypeRepMap sub ctx 
  ) => String -> LensM m (E Void2 sub ctx a)
mkVar = fromString

--IsString (LensyM' m TypeRepMap (m a))
--IsString (LensyM' m TypeRepMap (E TypeRepMap m (Value Int)))


{- instance {-# OVERLAPPABLE #-} (Typeable a, Typeable m, MonadIO m) 
  => IsString (Lensy TypeRepMap (m a)) where
  fromString var = Lensy { getLens = lens (yield var) (flip $ insert var), varName = var } -}


{- 
instance MonadIO m => ShowM m  TypeRepMap where
  showM (TypeRepMap m) =  do
    m' <-  (fmap . fmap) (\(a,(b,_)) -> a <> " -> " <> show b ) 
      . liftIO . (traverse . traverse . traverse) (fmap (maybe undefined id) .  tryReadMVar) . filter (\(a,_) -> a /= "sum") .  M.toList $ m
    let s = case  m' of
          (x:xs) -> foldl1' (\a b -> a <> ", " <> b) $ x :| xs
          [] -> ""
    
    pure $ "{ " <> s <> " }" -}

instance MonadIO m => ShowM m  (TypeRepMap sub ctx) where
  showM (TypeRepMap m) =  -- pure "env"
    pure . show . M.keys $ m 



