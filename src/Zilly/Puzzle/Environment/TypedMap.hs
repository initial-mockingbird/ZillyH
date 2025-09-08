{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeAbstractions     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ConstraintKinds      #-}
module Zilly.Puzzle.Environment.TypedMap where


import Data.Map (Map)
import qualified Data.Map as M


import Debug.Trace
import Control.Concurrent hiding (yield)
import Control.Monad.IO.Class
import Data.String (IsString(..))
import Data.Kind (Type)
import Control.Monad.Error.Class
import Zilly.Puzzle.Types.Exports

-------------------------------
-- Errors
--------------------------------


data GammaErrors
  =  VariableNotDefined String
  |  VariableAlreadyDeclared String
  |  VariableNotInitialized String

type EnvEffs m = (MonadIO m, MonadError String m)

showGammaError :: GammaErrors -> String
showGammaError (VariableNotDefined var) =
  "Variable '" <> var <> "' is not defined in the current scope."
showGammaError (VariableAlreadyDeclared var) =
  "Variable '" <> var <> "' is already declared in the current scope."
showGammaError (VariableNotInitialized var) =
  "Variable '" <> var <> "' is not initialized. Please ensure it has a value before accessing it."


--------------------------------
-- Lens interface
--------------------------------

type family EvalMonad (f :: Type) :: Type -> Type

type family VarMetadata (f :: Type) :: Type

class HasLType (f :: Type) where
  varLType :: String -> TypeRepMap f -> (EvalMonad f) Types

-- Defines a way to get, set, set fresh and obtain the name of a variable
data LensM (f :: Type) = LensM
  { getL        ::  TypeRepMap f -> (EvalMonad f) f
  , setL        ::  TypeRepMap f -> f -> VarMetadata f -> (EvalMonad f) (TypeRepMap f)
  , declareL    ::  TypeRepMap f -> VarMetadata f -> (EvalMonad f) (TypeRepMap f)
  , setFreshL   ::  TypeRepMap f -> f -> VarMetadata f -> (EvalMonad f) (TypeRepMap f)
  , varNameM    :: String
  , varMetadata :: TypeRepMap f -> (EvalMonad f) (VarMetadata f)
  }

viewMetadata :: LensM f -> TypeRepMap f -> (EvalMonad f) (VarMetadata f)
viewMetadata  = varMetadata

viewM :: LensM f -> TypeRepMap f -> (EvalMonad f) f
viewM  = getL

setM :: LensM f -> f -> VarMetadata f -> TypeRepMap f -> (EvalMonad f) (TypeRepMap f)
setM (LensM {setL=set}) f md m = set m f md

declareM :: LensM f -> VarMetadata f -> TypeRepMap f -> (EvalMonad f) (TypeRepMap f)
declareM (LensM {declareL=dec})  md m = dec m  md


data TypeRepMapElem f = TypeRepMapElem
  { elemMVar     :: MVar f
  , elemMetadata :: VarMetadata f
  }

newtype TypeRepMap f = TypeRepMap (Map String (TypeRepMapElem f))

empty :: TypeRepMap f
empty = TypeRepMap M.empty

scope :: TypeRepMap f -> [String]
scope (TypeRepMap m) = M.keys m

isInScope :: String -> TypeRepMap ctx -> Bool
isInScope s (TypeRepMap m) = s `M.member` m


fromList :: [(String, MVar f, VarMetadata f)] -> TypeRepMap f
fromList xs = TypeRepMap $ M.fromList $ map (\(var, mv, md) -> (var, TypeRepMapElem {elemMVar = mv, elemMetadata = md})) xs

toList :: TypeRepMap f -> [(String, MVar f, VarMetadata f)]
toList (TypeRepMap m) = M.toList m >>= \(var, TypeRepMapElem {elemMVar=mv, elemMetadata=md}) -> [(var, mv, md)]

undefineVar :: String -> TypeRepMap f -> TypeRepMap f
undefineVar var (TypeRepMap m) = TypeRepMap $ M.delete var m

reassign :: forall f m.
  ( MonadIO m
  , MonadError String m
  ) => String -> f -> TypeRepMap f -> m (TypeRepMap f)
reassign var f (TypeRepMap m) = case M.lookup var m of
  Just (TypeRepMapElem {elemMVar=mv}) -> do
      liftIO $ tryTakeMVar mv >> putMVar mv f
      pure . TypeRepMap $ m
  Nothing -> throwError . showGammaError $ VariableNotDefined var

reassignWith :: forall f m.
  ( MonadIO m
  , MonadError String m
  ) => String -> (f -> f ) -> TypeRepMap f -> m (TypeRepMap f)
reassignWith var f (TypeRepMap m) = case M.lookup var m of
  Just (TypeRepMapElem {elemMVar=mv}) -> do
      liftIO $ takeMVar mv >>= putMVar mv . f
      pure . TypeRepMap $ m
  Nothing -> throwError . showGammaError $ VariableNotDefined var

insertFresh :: forall  f m.
  (  MonadIO m
  ) => VarMetadata f -> String -> f  -> TypeRepMap f -> m (TypeRepMap f )
insertFresh t var val (TypeRepMap m) = do
    mv <- liftIO $ newMVar val
    let val' = TypeRepMapElem
          { elemMVar     = mv
          , elemMetadata = t
          }
    pure . TypeRepMap $ M.insert var val' m

declare :: forall  f m.
  ( MonadIO m
  , MonadError String m
  ) => VarMetadata f -> String -> TypeRepMap f -> m (TypeRepMap f)
declare t var (TypeRepMap m) = case M.lookup var m of
  Just _ -> throwError . showGammaError $ VariableAlreadyDeclared var
  Nothing -> do
    mv <- liftIO $ newEmptyMVar @f
    let val' = TypeRepMapElem
          { elemMVar     = mv
          , elemMetadata = t
          }
    !x <- pure . TypeRepMap $ M.insert var val' m
    pure x

declareFresh :: forall  f m.
  ( MonadIO m
  , MonadError String m
  ) => VarMetadata f -> String -> TypeRepMap f -> m (TypeRepMap f)
declareFresh t var (TypeRepMap m) = do
    mv <- liftIO $ newEmptyMVar @f
    let val' = TypeRepMapElem
          { elemMVar     = mv
          , elemMetadata = t
          }
    !x <- pure . TypeRepMap $ M.insert var val' m
    pure x



insertOrDeclare :: forall f m.
  ( MonadIO m
  , MonadError String m
  ) => VarMetadata f -> String -> f -> TypeRepMap f -> m (TypeRepMap f)
insertOrDeclare t var val (TypeRepMap m) = case M.lookup var m of
  Just (TypeRepMapElem {elemMVar=mv}) -> do
    _ <- liftIO $ tryTakeMVar mv
    liftIO $ putMVar mv val
    pure $ TypeRepMap m
  Nothing -> insertFresh t var val (TypeRepMap m)

yield :: forall f m.
  ( MonadIO m
  , MonadError String m
  ) => String -> TypeRepMap f  -> m f
yield var (TypeRepMap m) =
  case M.lookup var m of
    Just (TypeRepMapElem {elemMVar=mv})  -> liftIO (tryReadMVar mv) >>= \case
        Nothing -> (error $ "Var " <> show var <> " not inizialited" )
        Just e -> pure  e
    Nothing ->  throwError . showGammaError $ VariableNotDefined var

yieldMetadata :: forall f m.
  ( MonadIO m
  , MonadError String m
  ) => String -> TypeRepMap f -> m (VarMetadata f)
yieldMetadata var (TypeRepMap m) =
  case M.lookup var m of
    Just (TypeRepMapElem {elemMetadata=md}) -> pure md
    Nothing -> throwError . showGammaError $ VariableNotDefined var

instance forall  f.
  ( MonadIO (EvalMonad f)
  , MonadError String (EvalMonad f)
  ) => IsString (LensM f ) where
  fromString var =  LensM
    { getL     = yield  var
    , setL     = \m f md -> insertOrDeclare md var f m
    , declareL = \m md -> declare md var m
    , varNameM = var
    , varMetadata = yieldMetadata var
    , setFreshL = \m f md -> insertFresh md var f m
    }


mkVar :: forall   f.
  ( MonadIO (EvalMonad f)
  , MonadError String (EvalMonad f)
  ) => String -> LensM f
mkVar = fromString

class HasTypeRepMap f where
  getEnv :: (EvalMonad f) (TypeRepMap f)
  withEnv :: TypeRepMap f -> (EvalMonad f) a -> (EvalMonad f) a
