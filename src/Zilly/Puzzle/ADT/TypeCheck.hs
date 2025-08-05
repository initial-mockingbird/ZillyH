{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ViewPatterns #-}

module Zilly.Puzzle.ADT.TypeCheck where

import Zilly.Puzzle.Parser
import Zilly.Puzzle.Newtypes qualified as T
import Zilly.Puzzle.ADT.Expression
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.ADT.Action

import Data.Set (Set)
import Data.Set qualified as S
import Prelude.Singletons
import Data.Singletons.TH
import Debug.Trace (trace)
import Data.Matchers
import Data.Traversable
import Control.Monad.Error.Class
import Data.Text (Text)
import Data.Text qualified as Text
import Data.String (IsString(..))
import Data.List (intercalate)
import Data.Default
import Data.Foldable

reportTCError :: MonadError String m
  => BookeepInfo -> Set T.Types -> T.Types -> m a
reportTCError bk expected actual =
  throwError $ "Type error at " ++ show (tokenPos bk) ++ ". Any of the types: " ++ showExpected expected ++ " were expected, but instead got " ++ show actual
  where
   showExpected :: Set T.Types -> String
   showExpected = intercalate ", "  . fmap show . S.toList

class Monad m => TCMonad m where
  withExpectedType :: Set T.Types -> m a -> m a
  getExpectedType :: m (Set T.Types)
  validateType :: BookeepInfo -> T.Types -> m ()

type TCEffs ctx m =
  ( TCMonad m
  , ACtxConstraint ctx m
  )

tcAs :: forall {m} ctx f.
  ( Foldable f
  , TCEffs ctx m
  )
  => TypeRepMap (E ctx)
  -> f (A0 ParsingStage)
  -> m (TypeRepMap (E ctx), [A ctx])
tcAs ienv as = foldlM (\(env, acc) a -> do
  (a', env') <- withEnv env $ tcA0 a
  pure (env', acc ++ [a'])) (ienv, []) as

tcA0 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => A0 ParsingStage -> m (A ctx, TypeRepMap (E ctx))
tcA0 (Decl ltype (yieldVarName -> Just v) r bk) = do
  env <- getEnv
  env' <- declare ltype v env
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) v
  (r', rt) <- withEnv env'
    $ withExpectedType (S.singleton ltype)
    $ tcE @_ @ctx r
  env'' <- reassign v r' env'
  pure (Zilly.Puzzle.ADT.Action.Assign ltype var r', env'')
tcA0 (Zilly.Puzzle.Parser.Assign (yieldVarName -> Just v) r bk) = do
  env <- getEnv
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) v
  case v `isInScope` env of
    False -> throwError $ showGammaError (VariableNotDefined v)
    True -> do
      ltype <- varMetadata var env
      (r', rt) <- withExpectedType (S.singleton ltype) $ tcE @_ @ctx r
      -- env' <- reassign v r' env
      pure (Reassign var r', env)
tcA0 (Zilly.Puzzle.Parser.Print e bk) = do
  env <- getEnv
  (e', et) <- withExpectedType S.empty $ tcE @_ @ctx e
  pure (Zilly.Puzzle.ADT.Action.Print e', env)
tcA0 (Zilly.Puzzle.Parser.SysCommand cmd bk) | cmd `elem` extensions = do
  env' <-  def @(m (TypeRepMap (E ctx)))
  pure (Zilly.Puzzle.ADT.Action.SysCommand cmd, env')
  where
    extensions =
      [ "reset"
      , "Einfix"
      , "EB"
      , "ER"
      , "ET"
        , "ES"
      , "EMApp"
      , "EMAbs"
      , "DB"
      , "DR"
      , "DT"
      , "DS"
      , "DMApp"
      , "DMAbs"
      , "Zilly"
      , "Zilly+"
      ]
tcA0 (Zilly.Puzzle.Parser.SysCommand cmd bk) = do
  throwError $ "Unknown system command: " ++ cmd ++ ". Supported commands are: " ++ intercalate ", " extensions
  where
    extensions =
      [ "reset"
      , "Einfix"
      , "EB"
      , "ER"
      , "ET"
      , "ES"
      , "EMApp"
      , "EMAbs"
      , "DB"
      , "DR"
      , "DT"
      , "DS"
      , "DMApp"
      , "DMAbs"
      , "Zilly"
      , "Zilly+"
      ]

tcE :: forall {m} n ctx.
  ( TCEffs ctx m
  , SingI n
  )
  => EPrec ParsingStage n -> m (E ctx, T.Types)
tcE e = case () of
  () | Just Refl <- matches @0 (sing @n) -> tcE0 e
     | Just Refl <- matches @1 (sing @n) -> tcE1 e
     | Just Refl <- matches @3 (sing @n) -> tcE3 e
     | Just Refl <- matches @4 (sing @n) -> tcE4 e
     | Just Refl <- matches @6 (sing @n) -> tcE6 e
     | Just Refl <- matches @7 (sing @n) -> tcE7 e
     | Just Refl <- matches @8 (sing @n) -> tcE8 e
     | Just Refl <- matches @PrefixPrec (sing @n) -> tcEPrefixPrec e
     | Just Refl <- matches @PostfixPrec (sing @n) -> tcEPostfixPrec e
     | Just Refl <- matches @Atom (sing @n) -> tcEAtom e
     | otherwise -> error $ "Type checking for " ++ show (sing @n) ++ " is not implemented yet."

tcEAtom :: forall {m} ctx.
  ( TCMonad m
  , ACtxConstraint ctx m
  )
  => EPrec ParsingStage Atom -> m (E ctx,T.Types)
tcEAtom (PInt bk n) = do
  validateType bk T.Z
  pure (ValZ n, T.Z)
tcEAtom (PFloat bk n) = do
  validateType bk T.F
  pure (ValF n, T.F)
tcEAtom (PBool bk b) = do
  validateType bk T.ZBool
  pure (ValB b, T.ZBool)
tcEAtom (PString bk s) = do
  validateType bk T.ZString
  pure (ValS s, T.ZString)
tcEAtom (PVar bk v) = do
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) v
  env <- getEnv
  case v `isInScope` env of
    False -> throwError $ showGammaError (VariableNotDefined v)
    True -> do
      ltype <- varMetadata var env
      let rtype = T.rtype ltype
      validateType bk rtype
      pure (Var var, rtype)
tcEAtom (PTuple bk a b xs) = do
  let isTuple t = case t of
        T.NTuple _ _ _ -> True
        _ -> False
      f1 t = case t of
        T.NTuple a1 _ _ -> a1
        _ -> t
      f2 t = case t of
        T.NTuple _ b1 _ -> b1
        _ -> t
      fns t = case t of
        T.NTuple _ _ xs1 -> xs1
        _ -> []
  eTuples' <- S.filter isTuple <$> getExpectedType
  let etaStud = T.TVar (T.TV "x1")
  let etbStud = T.TVar (T.TV "x2")
  let stud = [T.TVar (T.TV $ "x" <> Text.pack (show i)) | i <- fmap fst ([3..] `zip` xs)]
  let eTuples = if null eTuples' then (T.NTuple etaStud etbStud stud) else S.elemAt 0 eTuples'
  let eta = f1  $ eTuples
  let etb = f2  $ eTuples
  let ets = fns $ eTuples
  (a',at') <- withExpectedType (S.singleton eta) $ tcE @_ @ctx a
  (b',bt') <- withExpectedType (S.singleton etb) $ tcE @_ @ctx b
  let
      f :: forall targs. SingI targs => [EPrec ParsingStage targs] -> [T.Types] -> m [(E ctx, T.Types)]
      f xs etxs = case (xs,etxs) of
          (x:xs, etx:etxs) -> (:) <$> withExpectedType (S.singleton etx) (tcE @_ @ctx x) <*> f xs etxs
          ([], []) -> pure []
          _ -> reportTCError bk (S.singleton $ T.NTuple etaStud etbStud ets) (T.NTuple at' at' stud)
  (xs', ets') <- unzip <$> f xs ets
  let t = T.NTuple at' bt' ets'
  pure  (MkTuple a' b' xs', t)

tcEAtom (PParen _ a) = tcE a
tcEAtom (PDefer _ a) = do
  eta <- S.map T.rtype <$> getExpectedType
  (a',at') <- withExpectedType eta $ tcE a
  pure (Defer a', T.Lazy at')
tcEAtom (PIf bk (a, b, c)) = do
  (a',at') <- withExpectedType (S.fromList [T.Z,T.F,T.ZBool]) $ tcE a
  (b',bt') <- tcE b
  (c',ct') <- tcE c
  case at' of
    T.ZBool -> pure ()
    T.Z     -> pure ()
    T.F     -> pure ()
    _ -> reportTCError bk (S.singleton T.ZBool) at'
  pure (If a' b' c', bt')

tcEPrefixPrec :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage PrefixPrec -> m (E ctx, T.Types)
tcEPrefixPrec (PUMinus _ a) = do
  ets' <- getExpectedType
  let ets = if null ets' then S.fromList [T.Z, T.F] else ets'
  (a', at') <- withExpectedType ets $ tcE @_ @ctx a
  pure (MinusU a', at')
tcEPrefixPrec (PNegate _ a) = do
  ets' <- getExpectedType
  let ets = if null ets' then S.singleton T.ZBool else ets'
  (a', at') <- withExpectedType ets $ tcE @_ @ctx a
  pure (Negate a', at')
tcEPrefixPrec (OfHigherPrefixPrec  a) = tcE a

tcEPostfixPrec :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage PostfixPrec -> m (E ctx, T.Types)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "formula") [arg]) | Just varN <- yieldVarName arg  = do
  (arg', at) <-  tcE arg
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) varN
  env <- getEnv
  ltype <- varMetadata var env
  validateType bk ltype
  pure (Formula $$ arg', ltype)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "random") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $  tcE arg
  validateType bk at
  pure (Random $$ arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "_1") [arg]) = do
  (arg', at) <- withExpectedType S.empty $  tcE arg
  case at of
    T.NTuple a _ _ -> validateType bk a
    _ -> withExpectedType
      (S.singleton $ T.NTuple (T.TVar (T.TV "x1")) (T.TVar (T.TV "x2")) [])
      $ validateType bk at
  pure (A_1 arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "_2") [arg]) = do
  (arg', at) <- withExpectedType S.empty $  tcE arg
  case at of
    T.NTuple _ b _ -> validateType bk b
    _ -> withExpectedType
      (S.singleton $ T.NTuple (T.TVar (T.TV "x1")) (T.TVar (T.TV "x2")) [])
      $ validateType bk at
  pure (A_2 arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "fst") arg) =
  tcEPostfixPrec $ PApp bk (OfHigherPostfixPrec $ PVar @ParsingStage bk "_1") arg
tcEPostfixPrec (PApp bk (yieldVarName -> Just "snd") arg) =
  tcEPostfixPrec $ PApp bk (OfHigherPostfixPrec $ PVar @ParsingStage bk "_2") arg
tcEPostfixPrec (PApp bk (yieldVarName -> Just "head") [arg]) = do
  (arg', at) <- tcE arg
  pure (Head $$ arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "tail") [arg]) = do
  (arg', at) <- tcE arg
  pure (Tail $$ arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "log") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (LogE  arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "sin") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (Sin  arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "cos") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (Cos arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "tan") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (Tan arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "asin") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (ASin arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "acos") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (ACos arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "atan") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $ tcE arg
  validateType bk at
  pure (ATan arg', at)

tcEPostfixPrec (PApp bk f [arg]) = do
  (f',ft)   <- withExpectedType S.empty $ tcE f
  (arg',at) <- withExpectedType S.empty $ tcE arg
  case ft of
    x T.:-> y | at `T.isSubtypeOf` x -> do
      validateType bk y
      pure (App f' arg', y)
    x T.:-> y ->
        reportTCError bk (S.singleton $ x ) at
    _ -> reportTCError bk (S.singleton $ (T.TVar (T.TV "x1") T.:->  T.TVar (T.TV "x2") )) ft
tcEPostfixPrec (PAppArr bk _ _) = throwError $ "Array application is not supported in type checking."
tcEPostfixPrec (OfHigherPostfixPrec a) = tcE a


tcE8 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 8 -> m (E ctx, T.Types)
tcE8 (PPower bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  let ub = if lt `T.isSubtypeOf` rt then lt else rt
  validateType bk ub
  pure (PowInfix l' r', ub)
tcE8 (OfHigher8 a) = tcE a

tcE7 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 7 -> m (E ctx, T.Types)
tcE7 (PMul bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  let ub = if lt `T.isSubtypeOf` rt then lt else rt
  validateType bk ub
  pure (TimesInfix l' r', ub)
tcE7 (PDiv bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  let ub = if lt `T.isSubtypeOf` rt then lt else rt
  validateType bk ub
  pure (DivInfix l' r', ub)
-- tcE7 (PMod bk l r) = do
--   (l', lt) <- withExpectedType (S.fromList [T.Z]) $ tcE @_ @ctx l
--   (r', rt) <- withExpectedType (S.fromList [T.Z]) $ tcE @_ @ctx r
--   let ub = if lt `T.isSubtypeOf` rt then lt else rt
--   validateType bk ub
--   pure (ModInfix l' r', ub)
tcE7 (PMod bk l r) = throwError $ "Modulus operator is not supported."
tcE7 (OfHigher7 a) = tcE a


tcE6 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 6 -> m (E ctx, T.Types)
tcE6 (PPlus bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  let ub = if lt `T.isSubtypeOf` rt then lt else rt
  validateType bk ub
  pure (PlusInfix l' r', ub)
tcE6 (PMinus bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  let ub = if lt `T.isSubtypeOf` rt then lt else rt
  validateType bk ub
  pure (MinusInfix l' r', ub)
tcE6 (PAppend bk l r) = do
  (l', lt) <- withExpectedType (S.singleton T.ZString) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.singleton T.ZString) $ tcE @_ @ctx r
  validateType bk T.ZString
  pure (AppendInfix l' r', T.ZString)
tcE6 (OfHigher6 a) = tcE a


tcE4 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 4 -> m (E ctx, T.Types)
tcE4 (PLT bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (LTInfix l' r', T.ZBool)
tcE4 (PLTEQ bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (LEInfix l' r', T.ZBool)
tcE4 (PEQ bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z,T.ZString,T.ZBool]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z,T.ZString,T.ZBool]) $ tcE @_ @ctx r
  let ub = if lt `T.isSuperTypeOf` rt then lt else rt
  validateType bk T.ZBool
  pure (EQInfix l' r', T.ZBool)
tcE4 (PGT bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (GTInfix l' r', T.ZBool)
tcE4 (PGTEQ bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z]) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (GEInfix l' r', T.ZBool)
tcE4 (PNEQ bk l r) = do
  (l', lt) <- withExpectedType (S.fromList [T.F,T.Z,T.ZString,T.ZBool]) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.fromList [T.F,T.Z,T.ZString,T.ZBool]) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (NEInfix l' r', T.ZBool)
tcE4 (OfHigher4 a) = tcE a

tcE3 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 3 -> m (E ctx, T.Types)
tcE3 (PAnd bk l r) = do
  (l', lt) <- withExpectedType (S.singleton T.ZBool) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.singleton T.ZBool) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (AndInfix l' r', T.ZBool)
tcE3 (POr bk l r) = do
  (l', lt) <- withExpectedType (S.singleton T.ZBool) $ tcE @_ @ctx l
  (r', rt) <- withExpectedType (S.singleton T.ZBool) $ tcE @_ @ctx r
  validateType bk T.ZBool
  pure (OrInfix l' r', T.ZBool)
tcE3 (OfHigher3 a) = tcE a

tcE1 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 1 -> m (E ctx, T.Types)
tcE1 (PLambda bk [(yieldVarName -> Just arg, gltype)] mgbody body) = do
  env <- getEnv
  env' <- declareFresh @(E ctx) gltype arg env
  let gbody = case mgbody of
        Nothing -> S.empty
        Just t  -> S.singleton t
  (body',bt) <- withEnv env' $ withExpectedType gbody $ tcE body
  validateType bk (gltype T.:-> bt)
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) arg
  pure (Lambda (gltype,mgbody) var body' , gltype T.:-> bt)
tcE1 (OfHigher1 a) = tcE a

tcE0 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 0 -> m (E ctx, T.Types)
tcE0 (OfHigher0 a) = tcE a
