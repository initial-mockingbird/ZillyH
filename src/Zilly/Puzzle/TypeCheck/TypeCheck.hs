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

module Zilly.Puzzle.TypeCheck.TypeCheck
  ( TCMonad(..)
  , TCEffs
  , tcAs
  , tcA0
  , tcE

  ) where

import Zilly.Puzzle.Parser
import Zilly.Puzzle.Types.Exports qualified as T
import Zilly.Puzzle.Expression.Exports
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Action.Exports
import Zilly.Puzzle.Patterns.Exports

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

reportTCError :: MonadError String m
  => BookeepInfo -> Set T.Types -> T.Types -> m a
reportTCError bk expected actual =
  throwError $ "Type error at " ++ show (tokenPos bk) ++ ". Any of the types: " ++ showExpected expected ++ " were expected, but instead got " ++ show actual
  where
  showExpected :: Set T.Types -> String
  showExpected = intercalate ", "  . fmap show . S.toList

implementsEQ :: T.Types -> Bool
implementsEQ t = case t of
  T.F -> True
  T.Z -> True
  T.ZString -> True
  T.ZBool -> True
  T.NDArray _ t -> implementsEQ t
  T.Tuple a b -> implementsEQ a && implementsEQ b
  T.Lazy t -> implementsEQ t
  T.ARecord fields -> all (implementsEQ . snd) fields
  _ -> False

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

tcProductConstructor :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => ProductConstructor -> m (String, [T.Types])
tcProductConstructor (MkProductConstructor consName consTypes) = do
  consTypes' <- forM consTypes $ \(_,ct) -> tcType @ctx ct
  pure (consName, consTypes')

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


tcA0 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => A0 ParsingStage -> m (A ctx, TypeRepMap (E ctx))
tcA0 (PTypeDef tn sop _) = do
  declareType tn []
  sop'  <- forM sop (tcProductConstructor @ctx . snd)
  unless (length (S.fromList (fmap fst sop')) == length sop') $
    throwError $ "Type " ++ tn ++ " has duplicate constructor names: " ++ show (fmap fst sop')
  updateType tn sop'
  env <- getEnv
  pure (TypeDef tn sop', env)

tcA0 (Decl ltype (yieldVarName -> Just v) r bk) = do
  env <- getEnv
  env' <- declare ltype v env
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) v
  (r', rt) <- withEnv env'
    $ withExpectedType (S.singleton ltype)
    $ tcE @_ @ctx r
  env'' <- reassign v r' env'
  pure (Zilly.Puzzle.Action.Exports.Assign ltype var r', env'')
tcA0 (Zilly.Puzzle.Parser.Assign (yieldArrAssign -> Just (v,ixss)) r bk) = do
  env <- getEnv
  ixsT <- forM ixss $ \ixs -> forM ixs $ \case
    PIndex e -> withExpectedType (S.singleton T.Z) $ (,Nothing) . fst <$> tcE @_ @ctx e
    PRangeIndexer (l,h) -> do
      (l', _) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx l
      (h', _) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx h
      pure (l', Just h')
  let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) v

  case v `isInScope` env of
    False -> throwError $ showGammaError (VariableNotDefined v)
    True -> do
      ltype <- varMetadata var env
      case mkEt ltype ixss of
        Just ltype' -> do
          (r', rt) <- withExpectedType (S.singleton ltype') $ tcE @_ @ctx r
          -- env' <- reassign v r' env
          pure (Reassign var ixsT r', env)
        Nothing -> throwError $ "Indexing error: " ++ show v ++ " with indices " ++ show ixss ++ " exceeds the dimensions of the type: " ++ show ltype
  where
  mkEt :: forall ctx. T.Types -> [[PIndexerExpression ctx]] -> Maybe T.Types
  mkEt t [] = Just t
  mkEt (T.NDArray n t) (ixs:ixss) = do
    let projectedDim = sum $ foldPIndexerExpression (\_ -> const 1) (const 0) <$> ixs
    let dim = length ixs
    when (dim /= n) $ Nothing
    let newT = if projectedDim == 0 then t else T.NDArray projectedDim t
    mkEt newT ixss

tcA0 (Zilly.Puzzle.Parser.Print e bk) = do
  env <- getEnv
  (e', et) <- withExpectedType S.empty $ tcE @_ @ctx e
  pure (Zilly.Puzzle.Action.Exports.Print e', env)
tcA0 (Zilly.Puzzle.Parser.SysCommand "tick" bk)  = do
  env' <-  getEnv
  pure (Zilly.Puzzle.Action.Exports.SysCommand "tick", env')

tcA0 (Zilly.Puzzle.Parser.SysCommand cmd bk) | cmd `elem` extensions = do
  env' <-  def @(m (TypeRepMap (E ctx)))
  pure (Zilly.Puzzle.Action.Exports.SysCommand cmd, env')
  where
    extensions =
      [ "reset"
      , "tick"
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
      , "tick"
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
tcA0 dec@(Decl {}) = throwError $ "Unsupported declaration: " ++ show dec
tcA0 ass@(Zilly.Puzzle.Parser.Assign {}) = throwError $ "Unsupported assignment: " ++ show ass

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
      pure (Var ltype var, rtype)
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
  pure  (MkTuple t a' b' xs', t)

tcEAtom (PParen _ a) = tcE a
tcEAtom (PDefer bk a) = do
  eta <- S.map T.rtype <$> getExpectedType
  (a',at') <- withExpectedType eta $ tcE a
  validateType bk $ T.Lazy at'
  pure (Defer (T.Lazy at') a', T.Lazy at')
tcEAtom (PIf bk (a, b, c)) = do
  (a',at') <- withExpectedType (S.fromList [T.Z,T.F,T.ZBool]) $ tcE a
  (b',bt') <- tcE b
  (c',ct') <- tcE c
  case at' of
    T.ZBool -> pure ()
    T.Z     -> pure ()
    T.F     -> pure ()
    _ -> reportTCError bk (S.singleton T.ZBool) at'
  ub <- case T.upperBound bt' ct' of
    Just ub -> pure ub
    Nothing -> throwError $ "Branches of if expression must have compatible types, but got: " ++ show bt' ++ " and " ++ show ct'
  pure (If ub a' b' c', bt')
tcEAtom (PArray bk xs) = do
  let isArray t = case t of
        T.NDArray _ _ -> True
        _ -> False
      fns t = case t of
        T.NDArray _ a1 -> a1
        _ -> t
  eArrs' <- S.filter isArray <$> getExpectedType
  (dimensions,bt) <- case null eArrs' of
    True  -> pure (1, T.TVar (T.TV "x1"))
    False -> let T.NDArray n a = S.elemAt 0 eArrs' in pure (n, a)

  let et = if dimensions == 1 then bt else T.NDArray (dimensions -1) bt
  (xs', ets') <- fmap unzip  $ forM xs $ \x -> withExpectedType (S.singleton et) $ tcE @_ @ctx x
  case dimensions == 1 of
    True -> pure (MkArray (T.NDArray 1 bt) $ A.fromList [length xs'] xs', T.NDArray 1 bt)
    False -> do
      xs'' <- for xs' $ \x' ->
        case x' of
          MkArray _ arr -> pure arr
          _ -> throwError $ "Expected an array literal, but got: " ++ show x'
      case xs'' of
        (r:rs) -> when (any (\a  -> A.shapeL a /= A.shapeL r) rs) $ do
          throwError $ "All array elements must have the same shape, but got: " ++ intercalate ", " (show <$> xs'')
        _ -> pure ()
      let shape = case xs'' of
            (r:_) -> length xs'' : A.shapeL r
            _     -> [length xs'']
      let res = A.reshape shape (A.concatOuter xs'')
      pure (MkArray (T.NDArray dimensions bt) $ res, T.NDArray dimensions bt)
tcEAtom (PECons bk cons args) = do
  ets <- getExpectedType
  possibleConsT <- filter (\p -> length args == length (snd p) ) <$> lookupCons cons
  let consTs  = transpose $ snd <$> possibleConsT
  args' <- forM (args `zip` consTs) $ \(arg, ets) ->
    withExpectedType (S.fromList ets) $ tcE @_ @ctx arg
  let argsT = fmap snd args'
      compatibleConsT
        = filter (\(t,ts)
            -> (t `S.member` ets || null ets)
            && all (uncurry $ T.isSuperTypeOf) (ts `zip` argsT)
            ) possibleConsT

  case compatibleConsT of
    [(t,_)] -> pure (Cons t cons (fst <$> args'), t)
    [] -> throwError
      $ "No compatible constructor found for "
      ++ cons
      ++ " with argument types: "
      ++ show argsT
      ++ " and expected types: "
      ++  (intercalate "," . fmap show . S.toList) ets
      ++ " at "
      ++ show (tokenPos bk)
    _  -> throwError
      $ "Ambiguous constructor "
      ++ cons
      ++ " with argument types: "
      ++ show argsT
      ++ " and expected types: "
      ++ show ets
      ++ ". Possible types are: "
      ++ intercalate ", " (fmap (show . fst) compatibleConsT)
      ++ " at "
      ++ show (tokenPos bk)
tcEAtom (PEARecord bk fields) = do
  let filterARecords t = case t of
        T.ARecord ts -> [ts]
        _ -> []
  ets
    <- filter (\ft -> all (\(k,_) -> Text.unpack k `elem` fmap fst fields) $  ft)
    . concatMap filterARecords
    . S.toList
    <$> getExpectedType

  fieldsWithTypes <- for fields $ \(k,e) -> do
      let et
            = S.fromList
            $ concatMap (\fts -> snd <$> filter (\(k',_) -> k' == Text.pack k) fts)
            ets
      (e',et') <- withExpectedType et $ tcE @_ @ctx e
      pure (k,e',et')

  let aRecordT = T.ARecord [(Text.pack k, et) | (k,_,et) <- fieldsWithTypes]
  let aRecord  = ARecord aRecordT [(k, e') | (k,e',_) <- fieldsWithTypes]
  validateType bk aRecordT
  pure (aRecord, aRecordT)
tcEAtom (PMatch bk e branches) = do
  (e',et) <- withExpectedType S.empty $ tcE @_ @ctx e
  branches' <- forM branches $ \(p,be) -> do
    (p',env) <- tcPattern et p
    (be',bt) <- withEnv env $ tcE @_ @ctx be
    pure (p', be', bt)

  let branchTypes = S.fromList $ fmap (\(_,_,t) -> t) branches'
      branchUB = foldl (\acc bt -> acc >>= T.upperBound bt) (Just T.Bot) branchTypes
  t <- getExpectedType
  case branchUB of
    Just T.Bot -> throwError $ "Branches of match expression must have compatible types, but got: " ++ show branchTypes
    Just ub -> case any (`T.isSuperTypeOf` ub) t || null t of
      True -> pure (Match ub e' [(p,be) | (p,be,_) <- branches'], ub)
      False -> reportTCError bk t ub
    Nothing -> throwError $ "Branches of match expression must have compatible types, but got: " ++ show branchTypes


tcLPattern :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => T.Types -> PLPattern ParsingStage -> m (LPattern ctx, TypeRepMap (E ctx))
tcLPattern t (PLVarPattern bk v) = do
  env <- getEnv
  env' <- declareFresh t v env
  pure (LVar v , env')
tcLPattern _ (PLWildcardPattern _) = (LWild,) <$> getEnv
tcLPattern T.Z (PLIntPattern bk n) = (LInt n, ) <$> getEnv
tcLPattern T.F (PLFloatPattern bk n) = (LFloat n, ) <$> getEnv
tcLPattern T.ZBool (PLBoolPattern bk b) = (LBool b, ) <$> getEnv
tcLPattern T.ZString (PLStringPattern bk s) = (LString s, ) <$> getEnv
tcLPattern (T.NTuple t1 t2 ts) (PLTuplePattern bk p1 p2 ps) | length ts == length ps = do
  (p1', env1) <- tcLPattern t1 p1
  (p2', env2) <- withEnv env1 $ tcLPattern t2 p2
  (ps', env3) <- foldlM (\(acc, env) (t,p) -> do
      (p', env') <- withEnv env $ tcLPattern t p
      pure (acc ++ [p'], env')
    ) ([], env2) (ts `zip` ps)
  let p1Vars = S.fromList $ lPatternVars p1'
      p2Vars = S.fromList $ lPatternVars p2'
      psVars = S.fromList . lPatternVars <$>  ps'
      psVars' = p1Vars : p2Vars : psVars
  case length (S.unions psVars') == sum (length <$> psVars') of
    True -> pure ()
    False -> throwError $ "A Variable in tuple pattern " ++ show (PLTuplePattern bk p1 p2 ps) ++ " is not unique."
  pure (LTuple p1' p2' ps', env3)
tcLPattern t (PLConstructorPattern bk con ps) = do
  mCons <- filter (\(t',_) -> t' == t) <$> lookupCons con
  env0 <- getEnv
  case mCons of
    [] -> throwError
      $ "Constructor " ++ con ++ " does not build type " ++ show t
      ++ " at " ++ show (tokenPos bk)
    [( _, consTs)] -> do
      when (length consTs /= length ps) $
        throwError $ "Constructor " ++ con ++ " expects " ++ show (length consTs) ++ " arguments, but got " ++ show (length ps) ++ " at " ++ show (tokenPos bk)
      (ps', env') <- foldlM (\(acc, env) (t',p) -> do
          (p', env') <- withEnv env $ tcLPattern t' p
          pure (acc ++ [p'], env')
        ) ([], env0) (consTs `zip` ps)
      let psVars = S.fromList . lPatternVars <$>  ps'
      case length (S.unions psVars) == sum (length <$> psVars) of
        True -> pure ()
        False -> throwError $ "A Variable in constructor pattern " ++ show (PLConstructorPattern bk con ps) ++ " is not unique."
      pure (LCons con ps', env')
    _  -> throwError $ "Ambiguous constructor " ++ con ++ " for type " ++ show t ++ " at " ++ show (tokenPos bk)
tcLPattern t@(T.ARecord fields) (PLARecordPattern bk fieldPatterns) = do
  let fieldMap = M.fromList fields
  for_ fieldPatterns $ \(k,fpt) -> case M.lookup (Text.pack k) fieldMap of
    Nothing -> throwError $ "Field " ++ k ++ " not found in record type " ++ show t ++ " at " ++ show (tokenPos bk)
    Just ft -> do
      unless (fpt `T.isSuperTypeOf` ft) $
        throwError $ "Field " ++ k ++ " in record pattern "
          ++ show (PLARecordPattern @ParsingStage bk fieldPatterns)
          ++ " has type " ++ show fpt
          ++ ", which is not compatible with expected type "
          ++ show ft ++ " at " ++ show (tokenPos bk)
      pure ()

  env <- getEnv
  env' <- foldlM (\envAcc (k,ft) -> do
      declareFresh ft k envAcc
    ) env fieldPatterns
  pure (LARecord fieldPatterns, env')
tcLPattern t p = throwError
  $ "Pattern " ++ show p ++ " is not compatible with expected type " ++ show t

tcPatternGuard :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => PPaternGuard ParsingStage -> m (PatternGuard (E ctx) ctx, TypeRepMap (E ctx))
tcPatternGuard (PExprGuard bk e) = do
  (e', _) <- withExpectedType (S.singleton T.ZBool) $ tcE @_ @ctx e
  (ExprGuard e', ) <$> getEnv
tcPatternGuard (PBindingGuard bk p e) = do
  (e',et) <- withExpectedType S.empty $ tcE @_ @ctx e
  (p', env') <- tcLPattern et p
  pure (BindingGuard p' e', env')

tcPattern :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => T.Types -> PPattern ParsingStage -> m (Pattern (E ctx) ctx, TypeRepMap (E ctx))
tcPattern t (MkPPattern lp gs) = do
  (lp', env1) <- tcLPattern t lp
  (gs', env2) <- foldlM (\(acc, env) g -> do
      (g', env') <- withEnv env $ tcPatternGuard g
      pure (acc ++ [g'], env')
    ) ([], env1) gs
  pure (Pattern lp' gs', env2)

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
tcEPostfixPrec (PApp bk (yieldVarName -> Just "formula") [arg])
  | Just (v,indexers) <- yieldArrAssign arg = do
      let var = Zilly.Puzzle.Environment.TypedMap.mkVar @(E ctx) v
      env <- getEnv
      case v `isInScope` env of
        False -> throwError $ showGammaError (VariableNotDefined v)
        True -> do
          ltype <- varMetadata var env
          let retT = arrType ltype indexers
          validateType bk retT
          (arg', at) <-  withExpectedType (S.singleton retT) $ tcE arg
          pure (Formula $$ arg', retT)
  where
    arrType :: T.Types -> [[PIndexerExpression ParsingStage]] -> T.Types
    arrType (T.NDArray n t) (ixs:ixss) =
      let projectedDim = sum $ foldPIndexerExpression (\_ -> const 1) (const 0) <$> ixs
          dim = length ixs
          newT = if projectedDim == 0 then t else T.NDArray projectedDim t
      in arrType newT ixss
    arrType t _ = t
tcEPostfixPrec (PApp bk (yieldVarName -> Just "formula") [arg]) = do
  (arg',argT) <- tcE arg
  pure (Formula $$ arg', argT)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "random") [arg]) = do
  (arg', at) <- withExpectedType (S.fromList [T.Z, T.F]) $  tcE arg
  validateType bk at
  pure (Random at $$ arg', at)
tcEPostfixPrec (PApp bk (yieldVarName -> Just "vector") [cols,fun]) = do
  let mkFunExpectedType t = T.Z T.:-> t
  let vunwrapper t = case t of
        T.NDArray n t' | n > 1 -> [t']
        T.TCon {} -> []
        _ -> [t]
  let etTransform = S.fromList . fmap mkFunExpectedType . concatMap vunwrapper . S.toList

  et <- getExpectedType
  (cols', bt) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx cols
  (fun', ft)  <- withExpectedType (etTransform et) $ tcE @_ @ctx fun
  case ft of
    T.Z T.:-> t ->pure (VectorSat cols' fun', T.NDArray 1 t)
    _ -> throwError "function type is not of the form Z -> t"
tcEPostfixPrec (PApp bk (yieldVarName -> Just "cons") [elem,arr]) = do
  (arr',arrt) <- tcE @_ @ctx arr
  case arrt of
    T.NDArray n t -> do
      (elem',et') <- withExpectedType (S.singleton t) $ tcE @_ @ctx elem
      pure (ConsSat elem' arr', arrt)
    _ -> reportTCError bk (S.singleton $ T.NDArray 1 $ T.TVar (T.TV "x1")) arrt
tcEPostfixPrec (PApp bk (yieldVarName -> Just "length") [arr]) = do
  validateType bk T.Z
  (arr',arrt) <- withExpectedType S.empty $ tcE @_ @ctx arr
  case arrt of
    T.NDArray {} -> do
      pure (Length arr', T.Z)
    _ -> reportTCError bk (S.singleton $ T.NDArray 1 $ T.TVar (T.TV "x1")) arrt
tcEPostfixPrec (PApp bk (yieldVarName -> Just "matrix") [rows,cols,fun]) = do
  let mkFunExpectedType t = T.Z T.:-> (T.Z T.:-> t)
  let vunwrapper t = case t of
        T.NDArray n t' | n > 1 -> [t']
        T.TCon {} -> []
        _ -> [t]
  let etTransform = S.fromList . fmap mkFunExpectedType . concatMap vunwrapper . S.toList


  et <- getExpectedType
  (rows', at) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx rows
  (cols', bt) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx cols
  (fun', ft)  <- withExpectedType (etTransform et) $ tcE @_ @ctx fun
  case ft of
    (T.Z T.:-> (T.Z T.:-> t)) ->pure (MatrixSat rows' cols' fun', T.NDArray 2 t)
    _ -> throwError "impossible: function type is not of the form Z -> Z -> t"
tcEPostfixPrec (PApp bk (yieldVarName -> Just "dim") [arr]) = do
  (arr',arrT) <- withExpectedType (S.empty) $ tcE @_ @ctx arr
  case arrT of
    T.NDArray n t -> do
      validateType bk (T.NDArray 1 T.Z)
      pure (Dim arr', T.NDArray 1 T.Z)
    _ -> reportTCError bk (S.singleton $ T.NDArray 1 $ T.TVar (T.TV "x1")) arrT


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
      pure (App y f' arg', y)
    x T.:-> y ->
        reportTCError bk (S.singleton $ x ) at
    _ -> reportTCError bk (S.singleton $ (T.TVar (T.TV "x1") T.:->  T.TVar (T.TV "x2") )) ft
tcEPostfixPrec (PApp _ _ _) = throwError $ "Function application must have exactly one argument."
tcEPostfixPrec (PAppArr bk arr ixs) = do
  let expectedDim = length ixs
  let projectedDim = sum $ foldPIndexerExpression (\_ -> const 1) (const 0) <$> ixs
  let mkProjectedType (T.NDArray n e) = do
        when (n /= expectedDim) $ throwError $ "Array slice error: expected " ++ show expectedDim ++ " dimensions, but got " ++ show n
        if projectedDim == 0 then pure e else pure (T.NDArray projectedDim e)
      mkProjectedType e = throwError $ "Array slice error: expected an array type, but got " ++ show e
  ixsT <- forM ixs $ \case
    PIndex e -> withExpectedType (S.singleton T.Z) $ (,Nothing) . fst <$> tcE @_ @ctx e
    PRangeIndexer (l,h) -> do
      (l', _) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx l
      (h', _) <- withExpectedType (S.singleton T.Z) $ tcE @_ @ctx h
      pure (l', Just h')
  (arr', at) <- withExpectedType S.empty $ tcE @_ @ctx arr
  at' <- mkProjectedType at
  validateType bk at'
  pure (ArraySlice at' arr' ixsT, at')
tcEPostfixPrec (PDotApp bk obj field) = do
  (obj', ot) <- withExpectedType S.empty $ tcE @_ @ctx obj
  case ot of
    T.ARecord fields -> case lookup (Text.pack field) fields of
      Just ft -> do
        validateType bk ft
        pure (DotApp ft obj' field, ft)
      Nothing -> throwError $ "Field " ++ field ++ " not found in record type " ++ show ot ++ " at " ++ show (tokenPos bk)
    t@(T.TCon tname _) -> lookupType (Text.unpack tname) >>= \case
      Just [(consName, [T.ARecord fields])] | Just ft <- lookup (Text.pack field) fields -> do
        validateType bk ft
        pure (DotApp ft obj' field, ft)
      Just (_:_:_) -> throwError
        $ "Type " ++ Text.unpack tname ++ " has multiple constructors, so field access is ambiguous at "
        ++ show (tokenPos bk)
      Just _ -> throwError $ "Type " ++ Text.unpack tname ++ " has no fields " ++ field ++ " at " ++ show (tokenPos bk)
      Nothing -> throwError $ "Type " ++ show t ++ " not found at " ++ show (tokenPos bk)

    _ -> reportTCError bk (S.singleton $ T.ARecord [(Text.pack "x1", T.TVar (T.TV "x2"))]) ot


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
  (l', lt) <- withExpectedType S.empty $ tcE @_ @ctx l
  (r', rt) <- withExpectedType S.empty $ tcE @_ @ctx r
  let ub = if lt `T.isSuperTypeOf` rt then lt else rt
  unless (lt `T.isSuperTypeOf` rt || lt `T.isSubtypeOf` rt) $ do
    throwError $ "Type error: " ++ show lt ++ " is not a supertype or subtype of " ++ show rt
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
  (l', lt) <- withExpectedType S.empty $ tcE @_ @ctx l
  (r', rt) <- withExpectedType S.empty $ tcE @_ @ctx r
  unless (lt `T.isSuperTypeOf` rt || lt `T.isSubtypeOf` rt) $ do
    throwError $ "Type error: " ++ show lt ++ " is not a supertype or subtype of " ++ show rt

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
  pure (Lambda (gltype T.:-> bt) (gltype,mgbody) var body' , gltype T.:-> bt)
tcE1 (PLambda bk _ _ _) = do
  throwError $ "Lambda expression must have at least one argument."
tcE1 (OfHigher1 a) = tcE a

tcE0 :: forall {m} ctx.
  ( TCEffs ctx m
  )
  => EPrec ParsingStage 0 -> m (E ctx, T.Types)
tcE0 (OfHigher0 a) = tcE a
