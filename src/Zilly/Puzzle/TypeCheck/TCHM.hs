{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances #-}

module Zilly.Puzzle.TypeCheck.TCHM where

import Zilly.Puzzle.Parser
import Zilly.Puzzle.Types.Exports qualified as T
import Zilly.Puzzle.Expression.Exports
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Action.Exports
import Zilly.Puzzle.Patterns.Exports
import Zilly.Puzzle.TypeCheck.HM
import Zilly.Puzzle.Parser qualified as Parser

import Data.Set (Set)
import Data.Set qualified as S
import Prelude.Singletons
import Data.Singletons.TH
import Data.Matchers
import Data.Traversable
import Control.Monad.Error.Class
import Data.Text qualified as Text
import Data.List (intercalate, transpose)
import Data.Default
import Data.Foldable
import Data.Array qualified as A
import Control.Monad
import Data.Maybe (fromMaybe)
import Data.Map qualified as M
import Control.Concurrent
import Control.Monad.IO.Class
import Data.Functor
import Debug.Trace (trace)

data TCTag prevCtx

type TCEffs ctx m =
  ( InferMonad m
  , ACtxConstraint ctx m
  )

data TCCtx prevCtx = MkTCCtx
  { _prevEnv :: ECtxMonoW prevCtx
  , _type :: MVar T.Types

  }

instance HasTypeInfo (TCCtx prevCtx) where
  getTypeInfo (MkTCCtx { _type = tVar }) = liftIO $ readMVar tVar
  setTypeInfo (MkTCCtx { _type = tVar }) t = liftIO $ tryTakeMVar tVar >> putMVar tVar t

instance
  ( HasBookeepInfo (ECtxMonoW prevCtx)
  )
  => HasBookeepInfo (TCCtx prevCtx) where
  getBookeepInfo (MkTCCtx { _prevEnv = prev }) = getBookeepInfo prev

type instance EIX (TCTag prevCtx) = TCCtx prevCtx
type instance EFX (TCTag prevCtx) = TCCtx prevCtx
type instance EBX (TCTag prevCtx) = TCCtx prevCtx
type instance ESX (TCTag prevCtx) = TCCtx prevCtx
type instance EVX (TCTag prevCtx) = TCCtx prevCtx
type instance ETX (TCTag prevCtx) = TCCtx prevCtx
type instance EPX (TCTag prevCtx) = TCCtx prevCtx
type instance EAX (TCTag prevCtx) = TCCtx prevCtx
type instance EDefX (TCTag prevCtx) = TCCtx prevCtx
type instance EIfX (TCTag prevCtx) = TCCtx prevCtx
type instance EMatchX (TCTag prevCtx) = TCCtx prevCtx
type instance EECons (TCTag prevCtx) = TCCtx prevCtx
type instance EARecordX (TCTag prevCtx) = TCCtx prevCtx
type instance EUMX (TCTag prevCtx) = TCCtx prevCtx
type instance ENegateX (TCTag prevCtx) = TCCtx prevCtx
type instance EAppX (TCTag prevCtx) = TCCtx prevCtx
type instance EAAppX (TCTag prevCtx) = TCCtx prevCtx
type instance EDAppX (TCTag prevCtx) = TCCtx prevCtx
type instance EPowX (TCTag prevCtx) = TCCtx prevCtx
type instance EMulX (TCTag prevCtx) = TCCtx prevCtx
type instance EDivX (TCTag prevCtx) = TCCtx prevCtx
type instance EModX (TCTag prevCtx) = TCCtx prevCtx
type instance EPlusX (TCTag prevCtx) = TCCtx prevCtx
type instance EMinusX (TCTag prevCtx) = TCCtx prevCtx
type instance EAppendX (TCTag prevCtx) = TCCtx prevCtx
type instance EPLTX (TCTag prevCtx) = TCCtx prevCtx
type instance EPLTEQX (TCTag prevCtx) = TCCtx prevCtx
type instance EPGTX (TCTag prevCtx) = TCCtx prevCtx
type instance EPGTEQX (TCTag prevCtx) = TCCtx prevCtx
type instance EPEQX (TCTag prevCtx) = TCCtx prevCtx
type instance EPNEQX (TCTag prevCtx) = TCCtx prevCtx
type instance EAndX (TCTag prevCtx) = TCCtx prevCtx
type instance EOrX (TCTag prevCtx) = TCCtx prevCtx
type instance ELambdaX (TCTag prevCtx) = TCCtx prevCtx
type instance PLVarCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLWCCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLIntCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLBoolCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLStringCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLFloatCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLTupleCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLConsCtx (TCTag prevCtx) = TCCtx prevCtx
type instance PLARecordCtx (TCTag prevCtx) = TCCtx prevCtx
type instance ExprGuardCtx (TCTag prevCtx) = TCCtx prevCtx
type instance BindingGuardCtx (TCTag prevCtx) = TCCtx prevCtx
type instance ASeqX (TCTag prevCtx) = TCCtx prevCtx
type instance ADeclX (TCTag prevCtx) = TCCtx prevCtx
type instance AAssignX (TCTag prevCtx) = TCCtx prevCtx
type instance APrintX (TCTag prevCtx) = TCCtx prevCtx
type instance ATDeclX (TCTag prevCtx) = TCCtx prevCtx
type instance SysCommandX (TCTag prevCtx) = TCCtx prevCtx



tcType :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => T.Types -> m T.Types
tcType = \case
  T.Z -> pure T.Z
  T.F -> pure T.F
  T.ZBool -> pure T.ZBool
  T.ZString -> pure T.ZString
  T.ZNull -> pure T.ZNull
  T.ZDouble -> pure T.F
  T.ZInfer -> pure $ T.ZInfer
  T.Lazy t -> T.Lazy <$> tcType @ctx t
  T.NDArray n t -> T.NDArray n <$> tcType @ctx t
  T.Tuple a b -> T.Tuple <$> tcType @ctx a <*> tcType @ctx b
  T.NTuple a b ts -> T.NTuple <$> tcType @ctx a <*> tcType @ctx b <*> mapM (tcType @ctx) ts
  (a T.:-> b) -> (T.:->) <$> tcType @ctx a <*> tcType @ctx b
  T.Top -> pure T.Top
  T.Bot -> pure T.Bot
  T.RV a -> T.RV <$> tcType @ctx a
  T.ARecord fields -> do
    unless ( length (S.fromList (fmap fst fields)) == length fields) $
      throwError $ "Record type has duplicate field names: " ++ show fields
    fields' <- forM fields $ \(k,t) -> (k,) <$> tcType @ctx t
    pure $ T.ARecord fields'
  T.TCon name ts -> T.TCon name <$> mapM (tcType @ctx) ts
  T.TFamApp name t ts -> T.TFamApp name <$> tcType @ctx t <*> mapM (tcType @ctx) ts
  T.TVar tv -> pure $ T.TVar tv


embedE :: forall n ctx m.
  ( SingI n
  , ECtxMono ctx
  , PatCtxMono ctx
  , MonadIO m
  , ECtxMonoW ctx ~ PatCtxMonoW ctx
  )
  => EPrec ctx n
  -> m (EPrec (TCTag ctx) n)
embedE e = do
  etVar :: MVar T.Types <- liftIO newEmptyMVar
  ptVar :: MVar T.Types <- liftIO newEmptyMVar
  let fe x = MkTCCtx
        { _prevEnv = x
        , _type = etVar
        }
  let fp y = MkTCCtx
        { _prevEnv = y
        , _type = ptVar
        }
  pure $ ePrecMorphism fe fp e


tcE' ::
  ( SingI n
  , InferMonad m
  )
  => EPrec (TCTag ctx) n
  -> m (EPrec (TCTag ctx) n, T.Types)
tcE' e = do
  !t <- infer e
  !cs <- getConstraints
  !subst <- solve emptySubst cs
  let !t' = apply subst t
  trace ("constraints: " <> show cs) pure ()
  trace ("Substitution: " <> show subst) pure ()
  trace ("Type after solving constraints: " <> show t') pure ()
  boundCheck t'
  pure (e, t')
-- tcE' e = (e,) <$> (infer e >>= \t ->  boundCheck t >> pure t)
-- tcE' e = (e,) <$> (infer e >>= \t -> pure t ) --boundCheck t >> pure t)


tcE ::
  ( SingI n
  , ECtxMono ctx
  , PatCtxMono ctx
  , InferMonad m
  , ECtxMonoW ctx ~ PatCtxMonoW ctx
  )
  => EPrec ctx n
  -> m (EPrec (TCTag ctx) n, T.Types)
tcE = embedE >=> tcE'

tcA ::
  ( ECtxMono ctx
  , PatCtxMono ctx
  , ACtxMono ctx
  , ECtxMonoW ctx ~ PatCtxMonoW ctx
  , ACtxMonoW ctx ~ ECtxMonoW ctx
  , InferMonad m
  )
  => A0 ctx
  -> m (A0 (TCTag ctx))
tcA (Decl t v e ctx) = do
  tv <- embedE v
  (e',te) <- tcE e
  trace ("Decl before unification: " <> show (T.mkRigid t) ) pure ()
  trace ("Decl rhs: " <> show (T.mkRigid te) ) pure ()
  subst <- unify (T.mkRigid te) (T.mkRigid t)
  let t' = apply subst te
  mt <- liftIO $ newMVar t'
  pure $ Decl t' tv e' (MkTCCtx ctx mt)
tcA (Parser.Assign v e ctx) = do
  tv <- embedE v
  (e',te) <- tcE e
  mt <- liftIO $ newMVar te
  pure $ Parser.Assign tv e' (MkTCCtx ctx mt)
tcA (Parser.Print e ctx) = do
  (e',te) <- tcE e
  liftIO $ putStrLn $ "Print statement has type: " ++ show te
  mt <- liftIO $ newMVar te
  pure $ Parser.Print e' (MkTCCtx ctx mt)
tcA (PTypeDef s cons ctx) = do
  mt <- liftIO $ newEmptyMVar
  pure $ PTypeDef s cons (MkTCCtx ctx mt)
tcA (Parser.SysCommand s ctx) = do
  mt <- liftIO $ newEmptyMVar
  pure $ Parser.SysCommand s (MkTCCtx ctx mt)



boundCheck :: InferMonad m => T.Types -> m ()
boundCheck (T.TConstraints cs _)
  | null cs   = pure ()
  | otherwise = (trace $ "cs: " <> show cs) for_ cs $ \case
      ("IsBoolean", t, _) ->
        case t of
          T.ZBool -> pure ()
          T.ZInfer -> pure ()
          T.TVar _ -> pure ()
          T.RV _ -> pure ()
          T.RTVar {} -> pure ()
          _ -> fail $ "Type " ++ show t ++ " is not a Boolean type."
      ("Eq", t, _) ->
        case t of
          T.Z -> pure ()
          T.ZBool -> pure ()
          T.ZString -> pure ()
          T.ZDouble -> pure ()
          T.ZNull -> pure ()
          T.TVar _ -> pure ()
          T.ZInfer  -> pure ()
          T.RV _ -> pure ()
          T.ZArray a -> boundCheck $ T.TConstraints (S.singleton ("Eq",a,[])) a
          T.NDArray _ a -> boundCheck $ T.TConstraints (S.singleton ("Eq",a,[])) a
          T.RTVar {} -> pure ()
          _ -> fail $ "Type " ++ show t ++ " does not implement Equality constraint."
      ("Num", t, _) ->
        case t of
          T.ZDouble -> pure ()
          T.TVar _ -> pure ()
          T.ZInfer  -> pure ()
          T.Z -> pure ()
          T.RV _ -> pure ()
          T.RTVar {} -> pure ()
          _ -> fail $ "Type " ++ show t ++ " does not implement Numeric constraint."
      ("Coerce", t, [target]) ->
        case (t, target) of
          (T.Z, T.ZDouble) -> pure ()
          (T.TVar _, _)    -> pure ()
          (T.ZInfer, _)    -> pure ()
          (_, T.TVar _)    -> pure ()
          (_, T.ZInfer)    -> pure ()
          (T.RV _, _)    -> pure ()
          (_, T.RV _)    -> pure ()
          (T.ZArray a, T.ZArray b) -> boundCheck $ T.TConstraints (S.singleton ("Coerce",a,[b])) a
          (T.NDArray n a, T.NDArray m b)
            | n >= m    -> boundCheck $ T.TConstraints (S.singleton ("Coerce",a,[b])) a
            | otherwise -> fail $ "Cannot coerce arrays of different dimensions: " ++ show t ++ " to " ++ show target ++ "."
          (T.Lazy a, b) -> boundCheck $ T.TConstraints (S.singleton ("Coerce",a,[b])) a
          (a, T.Lazy b) -> boundCheck $ T.TConstraints (S.singleton ("Coerce",a,[b])) a
          (a T.:-> b, c T.:-> d) -> do
            boundCheck $ T.TConstraints (S.singleton ("Coerce",c,[a])) a
            boundCheck $ T.TConstraints (S.singleton ("Coerce",b,[d])) b

          (T.RTVar {},_) -> pure ()
          (_,T.RTVar {}) -> pure ()
          _ -> fail $ "Cannot coerce type " ++ show t ++ " to " ++ show target ++ "."
      ("UpperBound", a, [b,ub]) -> trace ("UpperBound check: " <> show (a,b,ub)) $
        upperBoundM a b >>= flip unify ub >> pure ()
      ("LowerBound", a, [b,lb]) ->
        lowerBoundM a b >>= flip unify lb >> pure ()
      ("HasField", t, [T.StringDataKind fieldName, fieldType]) ->
        case t of
          T.ARecord fields ->
            case lookup fieldName fields of
              Just ft ->
                if ft == fieldType
                  then pure ()
                  else fail $ "Field " ++ Text.unpack fieldName ++ " in record type " ++ show t ++ " has type " ++ show ft ++ ", expected " ++ show fieldType ++ "."
              Nothing -> fail $ "Record type " ++ show t ++ " does not have field " ++ Text.unpack fieldName ++ "."
          T.TVar _ -> pure ()
          T.ZInfer -> pure ()
          T.RV _ -> pure ()
          T.RTVar {} -> pure ()
          _ -> fail $ "Type " ++ show t ++ " is not a record type."
      ("ImplementsRandom",a,[]) ->
        case a of
          T.Z -> pure ()
          T.ZDouble -> pure ()
          T.TVar _ -> pure ()
          T.ZInfer -> pure ()
          T.RV _ -> pure ()
          T.RTVar {} -> pure ()
          _ -> fail $ "Type " ++ show a ++ " does not implement Random constraint."
      ("BOrZ",a,[]) ->
        case a of
          T.ZBool -> pure ()
          T.Z -> pure ()
          T.TVar _ -> pure ()
          T.ZInfer -> pure ()
          T.RV _ -> pure ()
          T.RTVar {} -> pure ()
          _ -> fail $ "Type " ++ show a ++ " does not implement BOrZ constraint."
      ("~", a, [b]) -> pure ()
      t -> fail $ "Unknown constraint: " ++ show t
boundCheck _ = pure ()
