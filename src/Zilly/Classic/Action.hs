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

module Zilly.Classic.Action where

import Utilities.LensM
import Zilly.ADT.Expression
import Zilly.ADT.Action
import Zilly.Classic.Expression
import Zilly.Types
import Zilly.RValue
import Zilly.Upcast
import Zilly.Classic.Interpreter
import Utilities.TypedMap
import Utilities.ShowM
import Control.Monad.Reader

import Data.Kind (Type)
import Control.Monad.IO.Class
import Control.Monad
import Debug.Trace (trace)
import Control.Applicative (Alternative)
import Data.Singletons (SingI(..))
import Data.Traversable
import Utilities.TypedMap (empty)

data ActionTag
type instance AssocActionTag ActionTag = ExprTag


instance  Execute ActionTag  where 
  execInstruction ((:=) @_ @var @e var e) 
    = withSingIRType @var
    $ withSingIRType @e
    $ ubIsCommutative @(RValueT var) @(RValueT e)
    $ do
    gamma  <- declare @(RValueT var) @ExprTag (varNameM var) =<< ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast @ExprTag @(RValueT e) @(RValueT var) UpcastE rve of
      SameTypeUB  rve'     -> insert @(RValueT var) @ExprTag (varNameM var) rve' gamma
      RightUB     rve'     -> insert @(RValueT var) (varNameM var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT e) (varNameM var) rve' gamma
      SomethingElseUB rve' -> insert @_ (varNameM var) rve' gamma
    pure (var := e,gamma')
  execInstruction ((:=.) @_ @var @e var e) 
    = withSingIRType @var 
    $ withSingIRType @e 
    $ ubIsCommutative @(RValueT var) @(RValueT e)
    $ do
    gamma  <- ask
    rve    <- local (const gamma) $ rvalue e
    gamma' <- case upcast @ExprTag @(RValueT  e) @(RValueT  var) UpcastE rve of
      SameTypeUB  rve'     -> insert @(RValueT  var) @ExprTag (varNameM var) rve' gamma
      RightUB     rve'     -> insert @(RValueT  var) (varNameM var) rve' gamma
      LeftUB      rve'     -> insert @(RValueT  e) (varNameM var) rve' gamma
      SomethingElseUB rve' -> insert @_ (varNameM var) rve' gamma
    pure (var :=. e,gamma')
  execInstruction (OfExpr @_ @e e) 
    = withSingIRType @e
    $ withRVType @(AssocActionTag ActionTag) (sing @(RValueT e))
    $ do
    rve <- rvalue e
    gamma <- ask 
    pure (OfExpr rve, gamma)
  execInstruction (Print @_ @e e) 
    = withSingIRType @e 
    $ withRVType @(AssocActionTag ActionTag) (sing @(RValueT e))
    $ do
    rve <- rvalue e
    gamma <- ask 
    pure (Print rve, gamma)

execProgram :: forall t.
  ( Traversable t
  )
  => TypeRepMap ExprTag -> t (A ActionTag '()) -> (TaggedInterpreter ExprTag) (TypeRepMap ExprTag,t (A ActionTag '()))
execProgram ienv as = forAccumM ienv as $ \env a ->
  fmap (\(x,y) -> (y,x)) . local (const env) $ execInstruction @ActionTag a


--------------------------
-- Show instances
--------------------------

instance Monad m => ShowM m (A ActionTag a) where 
  showsPrecM p = \case
    (:=) @_ @ltype x e
      -> showStringM (withShow @ltype)
      <=< showCharM ' '
      <=< (showsPrecM p . UT . varNameM) x
      <=< showStringM " := "
      <=< showsM e
    (:=.) x e -> (showsPrecM p . UT . varNameM ) x <=< showStringM " := " <=< showsM e
    Print e   -> showsPrecM 10 e
    OfExpr e  -> showsM e


{-
execProgram :: forall t m a.
  ( Traversable t
  , Execute m
  , MonadIO m
  , Alternative m
  , ShowM m (A (TypeRepMap m ExprTag) m a)
  , MonadReader (TypeRepMap m ExprTag) m
  )
  => t (A (TypeRepMap m ExprTag) m a) -> m ()
execProgram = void . foldM (\env a -> local (const env) $ f a) empty
  where
    f :: A (TypeRepMap m ExprTag) m a -> m (TypeRepMap m ExprTag)
    f a = do
      (s,env) <- execInstruction a
      liftIO . putStrLn <=< showM $ a 
      liftIO $ putStrLn s 
      pure env -}
      

  
