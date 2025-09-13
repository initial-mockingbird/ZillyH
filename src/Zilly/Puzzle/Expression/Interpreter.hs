{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE TupleSections         #-}

module Zilly.Puzzle.Expression.Interpreter
  ( Effects
  , CtxConstraint
  , CtxPureConstraint
  , memoVal
  , evalE
  ) where


import Zilly.Puzzle.Types.Exports hiding (ARecord)
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Expression.Patterns
import Zilly.Puzzle.Expression.Classes
import Zilly.Puzzle.Expression.Show ()
import Zilly.Puzzle.Expression.Eq ()
import Zilly.Puzzle.Patterns.Exports
import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Random
import Zilly.Puzzle.Effects.CC
import Zilly.Puzzle.Effects.Memoize
import Control.Monad.Error.Class
import Data.Array
import Data.Traversable
import Data.Map qualified as M
import Data.Foldable (foldlM)



type Effects m =
  ( Functor m
  , Applicative m
  , Monad m
  , Alternative m
  , MonadIO m
  , MonadError String m
  , MonadRandom m
  , MonadCC m
  )

type CtxConstraint ctx m =
  ( EvalMonad (E ctx) ~ m
  , HasTypeRepMap (E ctx)
  , Effects m
  , CtxPureConstraint ctx
  )

type CtxPureConstraint ctx =
  ( HasArgType ctx LambdaTag
  , ArgType ctx LambdaTag ~ LambdaCtx ctx
  , HasRetType ctx LambdaTag
  , RetType ctx LambdaTag ~ LambdaCtx ctx
  , HasArgType ctx LambdaCTag
  , ArgType ctx LambdaCTag ~ LambdaCCtx ctx
  , HasRetType ctx LambdaCTag
  , RetType ctx LambdaCTag ~ LambdaCCtx ctx
  , LambdaCtx ctx ~ LambdaCCtx ctx
  , VarMetadata (E ctx) ~ Types
  )

fetchExpression :: forall {m} ctx.
  ( CtxConstraint ctx m
  ) => E ctx -> m (E ctx)
fetchExpression (Var _ l) = getEnv >>= getL l >>= fetchExpression
fetchExpression e       = pure e



memoVal :: forall {m} ctx.
  ( CtxConstraint ctx m
  ) => E ctx -> m (Memoized m (E ctx))
memoVal  = memoizeWithCC . evalE

evalE :: forall {m} ctx.
  ( CtxConstraint ctx m
  )
  => E ctx -> m (E ctx)
evalE e@(ValZ {})  = pure e
evalE e@(ValF {})  = pure e
evalE e@(ValB {})  = pure e
evalE e@(ValS {})  = pure e
evalE   (Var _ l  )  = getEnv >>= getL l >>= evalE
evalE (If _ c a b) = do
  mc' <- evalE c
  case mc' of
    Bottom t e0 es -> pure $ Bottom t e0 es
    ValZ c' ->
      case connectorZ c' of
        True  -> evalE a
        False -> evalE b
    ValF c' -> case connectorF c' of
      True  -> evalE a
      False -> evalE b
    ValB c' -> case c' of
      True  -> evalE a
      False -> evalE b

    _ -> throwError
      $ "Error on evaling 'if'-expression. Invalid condition: "
      <> show mc'
evalE (MkArray t es) = MkArray (rtype t) <$> traverse evalE es
evalE (Lambda t lctx arg body)
  = (\env -> LambdaC t lctx env arg body) <$> getEnv
evalE (Defer t a)   = do
  env <- getEnv
  ma <- memoizeWithCC $ withEnv env $ evalE a
  pure $ LazyC t env a ma
evalE (ArraySlice t earr eixs) = do
  ixs <- for eixs $ \(l,u) -> (,) <$> evalE @ctx l <*> traverse (evalE @ctx) u >>= \case
    (ValZ l', Just (ValZ u')) -> pure (l', Just u')
    (ValZ l', Nothing) -> pure (l', Nothing)
    (a',b') -> throwError
      $ "Error on evaling 'arraySlice' expression. Unsupported index: "
      <> show a' <> " and " <> show b'
  arr <- fetchExpression earr >>= \case
    MkArray _ es' -> pure  es'
    e' -> evalE e' >>= \case
      MkArray _ es'' -> pure es''
      e'' -> throwError
        $ "Error on evaling 'arraySlice' expression. Unsupported array: "
        <> show e''
  farr <- traverse (evalE @ctx) (slice' ixs arr)
  case shapeL farr of
    [] -> pure $ unScalar farr
    _  -> pure $ MkArray t farr
evalE (FormulaApp (Var _  x)) = getEnv >>= viewM x
evalE (FormulaApp (ArraySlice t earr eixs)) = do
  ixs <- for eixs $ \(l,u) -> (,) <$> evalE @ctx l <*> traverse (evalE @ctx) u >>= \case
    (ValZ l', Just (ValZ u')) -> pure (l', Just u')
    (ValZ l', Nothing) -> pure (l', Nothing)
    (a',b') -> throwError
      $ "Error on evaling 'arraySlice' expression. Unsupported index: "
      <> show a' <> " and " <> show b'
  fetchExpression earr >>= evalE . FormulaApp >>=  \case
    MkArray t' arr -> do
      let farr = slice' ixs arr
      case shapeL farr of
        [] -> pure $ unScalar farr
        _  -> pure $ MkArray t' farr
    e' -> pure $ ArraySlice t e' $ (\(a,b) -> (ValZ a, ValZ <$> b)) <$> ixs
evalE (FormulaApp e) = pure e
evalE (RandomApp x) = evalE x >>= \case
  Bottom t e0 es   -> pure $ Bottom t e0 es
  ValZ e' | e' < 1 -> pure $ ValZ 0
  ValZ e' -> ValZ <$> randInt e'
  ValF e' | e' < 0 -> pure $ ValF 0.0
  ValF e' -> ValF <$> randFloat e'
  e' -> throwError
    $ "Error on evaling 'random' expression. Unsupported argument: "
    <> show e'
evalE (Dim e) = evalE e >>= \case
  MkArray _ es -> pure . MkArray Z . (\xs -> Data.Array.fromList [length xs] xs)  . fmap ValZ . shapeL $ es
  Bottom t e0 es -> pure $ Bottom t e0 es
  e' -> throwError
    $ "Error on evaling 'dim' expression. Unsupported argument: "
    <> show e'
evalE (Length e) = evalE e >>= \case
  MkArray _ es -> pure . ValZ . size $  es
  Bottom t e0 es -> pure $ Bottom t e0 es
  e' -> throwError
    $ "Error on evaling 'length' expression. Unsupported argument: "
    <> show e'
evalE (MatrixSat r c f) = (,) <$> evalE r <*> evalE c >>= \case
  (ValZ r', ValZ c') | r' > 0 && c' > 0 -> do
    f' <- evalE f
    xs <- traverse evalE
      [ (f' $$ ValZ x) $$ ValZ y | x <- [0..r'-1], y <- [0..c'-1]]
    case typeOf f of
      (_ :-> _ :-> ret)
        -> pure $ MkArray ret $ Data.Array.fromList [r', c'] xs
      _ -> throwError
        $ "Error on evaling 'matrix' expression. Unsupported function type: "
        <> show (typeOf f)
  (ValZ r', ValZ c') -> throwError
    $ "Error on evaling 'matrix' expression. Invalid dimensions: "
    <> show r' <> " and " <> show c'
  (Bottom t e0 es, Bottom _ e1 es') -> pure $ Bottom t e0 (e1 : es <> es')
  (Bottom t e0 es, _)             -> pure $ Bottom t e0 es
  (_, Bottom t e1 es')            -> pure $ Bottom t e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'matrix' expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (VectorSat r f) = evalE r >>= \case
  ValZ r' | r' > 0 -> do
    f' <- evalE f
    case typeOf f of
      (_ :-> ret) -> do
          xs <- traverse evalE [App ret f' (ValZ x) | x <- [0..r'-1]]
          pure $ MkArray (NDArray 1 ret) $ Data.Array.fromList [r'] xs
      _ -> throwError
        $ "Error on evaling 'vector' expression. Unsupported function type: "
        <> show (typeOf f)

  ValZ r' -> throwError
    $ "Error on evaling 'vector' expression. Invalid dimension: "
    <> show r'
  Bottom t e0 es -> pure $ Bottom t e0 es
  e' -> throwError
    $ "Error on evaling 'vector' expression. Unsupported argument: "
    <> show e'
evalE (ConsSat h t) = (,) <$> evalE h <*> evalE t >>= \case
  (Bottom bt e0 es, Bottom _ e1 es') -> pure $ Bottom bt e0 (e1 : es <> es')
  (Bottom bt e0 es, _)             -> pure $ Bottom bt e0 es
  (_, Bottom bt e1 es')            -> pure $ Bottom bt e1 es'
  (h', MkArray tt' t')              -> pure $ MkArray tt' $ append (Data.Array.fromList [1] [h']) t'
  (_,e') -> throwError
    $ "Error on evaling 'cons' expression. Unsupported tail: "
    <> show e'
evalE (LTInfix a b) = binOPComp (<) (<) "lt" a b
evalE (LEInfix a b) = binOPComp (<=) (<=) "le" a b
evalE (GTInfix a b) = binOPComp (>) (>) "gt" a b
evalE (GEInfix a b) = binOPComp (>=) (>=) "ge" a b
evalE (EQInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (a',b') -> pure . ValB $ a' == b'
evalE (NEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (a',b') -> pure . ValB $ a' /= b'
evalE (LogE a) = evalE a >>= \case
  ValZ a' | a' <= 0 -> throwError "Error on evaling 'log'-expression. Logarithm of zero or negative number."
  ValF a' | a' <= 0 -> throwError "Error on evaling 'log'-expression. Logarithm of zero or negative number."
  ValZ a'           -> pure . ValF $ log (fromIntegral a')
  ValF a'           -> pure . ValF $ log a'
  Bottom bt e0 es      -> pure $ Bottom bt e0 es
  e'                -> throwError
    $ "Error on evaling 'log'-expression. Unsupported argument: "
    <> show e'
evalE (Sin a) = trigBuilder sin "sin" a
evalE (Cos a) = trigBuilder cos "cos" a
evalE (Tan a) = trigBuilder tan "tan" a
evalE (ASin a) = trigBuilder asin "asin" a
evalE (ACos a) = trigBuilder acos "acos" a
evalE (ATan a) = trigBuilder atan "atan" a
evalE (SubtractSat a b) = arithBuilder (flip (-)) (flip (-)) "subtractSat" a b
evalE (MinusInfix a b)  = arithBuilder (-) (-) "-" a b
evalE (PlusInfix a b)   = arithBuilder (+) (+) "+" a b
evalE (TimesInfix a b)  = arithBuilder (*) (*) "*" a b
evalE (DivInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> if b' == 0
    then throwError "Error on evaling '/'-expression. Division by zero."
    else pure . ValZ $ a' `div` b'
  (ValF a', ValF b') -> if b' == 0.0
    then throwError "Error on evaling '/'-expression. Division by zero."
    else pure . ValF $ a' / b'
  (ValZ a', ValF b') -> if b' == 0.0
    then throwError "Error on evaling '/'-expression. Division by zero."
    else pure . ValF $ fromIntegral a' / b'
  (ValF a', ValZ b') -> if b' == 0
    then throwError "Error on evaling '/'-expression. Division by zero."
    else pure . ValF $ a' / fromIntegral b'
  (Bottom bt  e0 es, Bottom _ e1 es') -> pure $ Bottom bt e0 (e1 : es <> es')
  (Bottom bt e0 es, _)             -> pure $ Bottom bt e0 es
  (_, Bottom bt e1 es')            -> pure $ Bottom bt e1 es'
  (a',b') -> throwError
    $ "Error on evaling '/'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (PowInfix a b) =
  binOP
    (^)
    (**)
    (\a' b' -> fromIntegral a' ** b')
    (^)
    ValZ
    ValF
    ValF
    ValF
    "^"
    a
    b
evalE (AppendInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValS a', ValS b') -> pure . ValS $ a' <> b'
  (Bottom t e0 es, Bottom _ e1 es') -> pure $ Bottom t e0 (e1 : es <> es')
  (Bottom t e0 es, _)             -> pure $ Bottom t e0 es
  (_, Bottom t e1 es')            -> pure $ Bottom t e1 es'
  (a',b') -> throwError
    $ "Error on evaling '++'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (AndInfix a b) = evalE a >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValB True -> evalE b >>= \case
    Bottom t' e1 es' -> pure $ Bottom t' e1 es'
    ValB b' -> pure . ValB $ b'
    b' -> throwError
      $ "Error on evaling '&&'-expression. Unsupported right argument: "
      <> show b'
  ValB False -> pure $ ValB False
  a' -> throwError
    $ "Error on evaling '&&'-expression. Unsupported left argument: "
    <> show a'
evalE (OrInfix a b) = evalE a >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValB True -> pure $ ValB True
  ValB False -> evalE b >>= \case
    Bottom t' e1 es' -> pure $ Bottom t' e1 es'
    ValB b' -> pure . ValB $ b'
    b' -> throwError
      $ "Error on evaling '||'-expression. Unsupported right argument: "
      <> show b'
  a' -> throwError
    $ "Error on evaling '||'-expression. Unsupported left argument: "
    <> show a'
evalE (Negate a) = evalE a >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValB a' -> pure . ValB $ not a'
  x' -> throwError
    $ "Error on evaling 'negate'-expression. Unsupported argument: "
    <> show x'
evalE (MinusU a) = evalE a >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValZ a' -> pure . ValZ $ -a'
  ValF a' -> pure . ValF $ -a'
  x' -> throwError
    $ "Error on evaling 'minusU'-expression. Unsupported argument: "
    <> show x'
evalE (HeadApp x) = evalE x >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValS [] -> pure $ ValS ""
  ValS (h:_) -> pure . ValS . pure $ h
  x' -> throwError
    $ "Error on evaling 'head'-expression. Non string argument: "
    <> show x'
evalE (TailApp x) = evalE x >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValS [] -> pure $ ValS ""
  ValS (_:xs) -> pure . ValS $ xs
  x' -> throwError
    $ "Error on evaling 'tail'-expression. Non string argument: "
    <> show x'
evalE (App _ (MinusUnsat _) x)  = unsatArithApp MinusInfix "minusUnsat" x
evalE (App _ (PlusUnsat _) x)   = unsatArithApp PlusInfix "plusUnsat" x
evalE (App _ (TimesUnsat _) x)  = unsatArithApp TimesInfix "timesUnsat" x
evalE (App _ (DivUnsat _) x)    = unsatArithApp DivInfix "divUnsat" x
evalE (App _ (PowUnsat _) x)    = unsatArithApp PowInfix "powUnsat" x
evalE (App _ AppendUnsat  x)    = evalE x >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValS a' -> (\env -> LambdaC (ZString :-> ZString) (ZString,Just ZString) env (mkVar @(E ctx) "x") (AppendInfix (ValS a') (FormulaApp (VarS ZString "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'appendUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App _ AndUnsat x) = evalE x >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValB b -> (\env -> LambdaC (ZBool :-> ZBool) (ZBool,Just ZBool) env (mkVar @(E ctx) "x") (AndInfix (ValB b) (FormulaApp (VarS ZBool "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'andUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App _ OrUnsat x) = evalE x >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValB b -> (\env -> LambdaC (ZBool :-> ZBool) (ZBool,Just ZBool) env (mkVar @(E ctx) "x") (OrInfix (ValB b) (FormulaApp (VarS ZBool "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'orUnsat'-expression. Unsupported argument: "
    <> show x
evalE (A_1 a) = evalE a >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  MkTuple _ a' _ _ -> pure $ a'
  _ -> throwError
    $ "Error on evaling 'A_1'-expression. Unsupported argument: "
    <> show a
evalE (A_2 a) = evalE a >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  MkTuple _ _ b' _ -> pure $ b'
  _ -> throwError
    $ "Error on evaling 'A_2'-expression. Unsupported argument: "
    <> show a
evalE f@(LambdaC {}) = pure $ f
evalE (LazyC _ _ _ mem)  = runMemoized mem
evalE b@(Bottom {})  = pure $ b
evalE (MkTuple t a b xs) = do
  a' <- evalE a
  b' <- evalE b
  xs' <- traverse evalE xs
  pure $ MkTuple (rtype t) a' b' xs'
evalE (App _ f x) = do
  mf' <- evalE f
  mx' <- evalE x
  case (mf',mx') of
    (Bottom bt e0 es, Bottom _ e1 es') -> pure  $ Bottom bt e0 (e1 : es <> es')
    (Bottom bt e0 es, _)             -> pure  $ Bottom bt e0 es
    (_, Bottom bt e1 es')            -> pure  $ Bottom bt e1 es'
    (LambdaC _ (t,_) env binded body,_)
      -> setFreshL binded env mx' t >>= \env' -> withEnv env' $ evalE body
    (Lambda _ (t,_) arg body, _)
      -> getEnv >>= \env -> setFreshL arg env mx' t >>= \env' -> withEnv env' $ evalE body

    _ -> error "Error on evaling 'function application'-expression. Function values can only be closures, subtyped functions, or bottom after reduction."
evalE (DotApp _ e field) = evalE e >>= \case
  Bottom bt e0 es -> pure $ Bottom bt e0 es
  ARecordV _ fields -> case lookup field fields of
    Just v  -> evalE v
    Nothing -> throwError
      $ "Error on evaling 'dot'-expression. Field '" <> field <> "' not found in record: "
      <> show e
  ConsRecordSingleV' _ fields -> case lookup field fields of
    Just v  -> evalE v
    Nothing -> throwError
      $ "Error on evaling 'dot'-expression. Field '" <> field <> "' not found in cons-record: "
      <> show e
  e' -> throwError
    $ "Error on evaling 'dot'-expression. Unsupported argument: "
    <> show e'
evalE (Cons t s es) = ConsV t s <$> traverse evalE es
evalE e@(ConsV {})  = pure e
evalE (ARecord t fields) = ARecordV t <$> (traverse . traverse) evalE fields
evalE e@(ARecordV {})    =  pure e
evalE (Match _ e branches) = do
  e' <- evalE e
  mr <- matchFirstAndEval branches e'
  case mr of
    Just v  -> pure v
    Nothing -> pure $ Bottom Bot (OtherError "Non-exhaustive patterns in match expression.") []

-- --------------------------
-- -- Aux Functions
-- --------------------------

data MatchResult = MatchSuccess | MatchFailure
  deriving (Eq, Show)


matchFirstAndEval :: forall {m} ctx
  . (CtxConstraint ctx m)
  => [ (Pattern (E ctx) ctx, E ctx) ] -> E ctx -> m (Maybe (E ctx))
matchFirstAndEval [] _ = pure Nothing
matchFirstAndEval ((p, e):ps) v = do
  (res, env') <- match p v
  case res of
    MatchFailure -> matchFirstAndEval ps v
    MatchSuccess -> Just <$> withEnv env' (evalE e)

match :: forall {m} ctx
  . (CtxConstraint ctx m)
  => Pattern (E ctx) ctx -> E ctx -> m (MatchResult, TypeRepMap (E ctx))
match (Pattern  lp guards) e = do
  env <- getEnv
  (res, env') <- matchLPattern env lp e
  case res of
    MatchFailure -> pure (MatchFailure, env)
    MatchSuccess -> go env env' guards
  where
    go :: TypeRepMap (E ctx) -> TypeRepMap (E ctx) -> [PatternGuard (E ctx) ctx] -> m (MatchResult, TypeRepMap (E ctx))
    go _ env' [] = pure (MatchSuccess, env')
    go failEnv env' (g:gs) = do
      (res', env'') <- matchPatternGuard env' g
      case res' of
        MatchSuccess -> go failEnv env'' gs
        MatchFailure -> pure (MatchFailure, failEnv)


matchLPattern :: forall {m} ctx
  . (CtxConstraint ctx m)
  => TypeRepMap (E ctx) -> LPattern ctx -> E ctx -> m (MatchResult, TypeRepMap (E ctx))
matchLPattern env (LVar  l) v = do
  newEnv <- insertFresh (typeOf v) l v env
  pure (MatchSuccess, newEnv)
matchLPattern env (LWild ) _ = pure (MatchSuccess, env)
matchLPattern env (LInt  n) (ValZ m)
  | n == m    = pure (MatchSuccess, env)
  | otherwise = pure (MatchFailure, env)
matchLPattern env (LBool  b) (ValB b')
  | b == b'   = pure (MatchSuccess, env)
  | otherwise = pure (MatchFailure, env)
matchLPattern env (LString  s) (ValS s')
  | s == s'   = pure (MatchSuccess, env)
  | otherwise = pure (MatchFailure, env)
matchLPattern env (LFloat  f) (ValF f')
  | f == f'   = pure (MatchSuccess, env)
  | otherwise = pure (MatchFailure, env)
matchLPattern env (LTuple  p1 p2 ps) (MkTuple _ v1 v2 vs) | length ps == length vs =
  go env (p1 : p2 : ps) (v1 : v2 : vs)
  where
    go env' [] [] = pure (MatchSuccess, env')
    go env' (p:ps') (v:vs') = do
      (res, env'') <- matchLPattern env' p v
      case res of
        MatchSuccess -> go env'' ps' vs'
        MatchFailure -> pure (MatchFailure, env)
    go env' _ _ = pure (MatchFailure, env')
matchLPattern env (LCons  name ps) (ConsV _ name' vs) | name == name' && length ps == length vs =
  go env ps vs
  where
    go env' [] [] = pure (MatchSuccess, env')
    go env' (p:ps') (v:vs') = do
      (res, env'') <- matchLPattern env' p v
      case res of
        MatchSuccess -> go env'' ps' vs'
        MatchFailure -> pure (MatchFailure, env)
    go _ _ _ = pure (MatchFailure, env)
matchLPattern env (LARecord  fields) (ARecordV _ vfields) = do
  mbindings <- fmap sequence $ for fields $ \(fname, ftype) -> case M.lookup fname fieldVMap of
      Nothing -> pure Nothing
      Just v  -> if typeOf v `isSubtypeOf` ftype then pure (Just (fname, v)) else pure Nothing
  case mbindings of
    Nothing -> pure (MatchFailure, env)
    Just bindings -> (MatchSuccess,) <$> foldlM (\env' (l,e) -> insertFresh (typeOf e) l e env') env bindings
  where
    fieldVMap = M.fromList vfields
matchLPattern env _ _ = pure (MatchFailure, env)

matchPatternGuard :: forall {m} ctx
  . (CtxConstraint ctx m)
  => TypeRepMap (E ctx) -> PatternGuard (E ctx) ctx -> m (MatchResult, TypeRepMap (E ctx))
matchPatternGuard env (ExprGuard  expr) = evalE expr >>= \case
  ValB True -> pure (MatchSuccess, env)
  _         -> pure (MatchFailure, env)
matchPatternGuard env (BindingGuard  lpattern expr) = do
  expr' <- evalE expr
  matchLPattern env lpattern expr'

connectorZ :: Int -> Bool
connectorZ = (/= 0)

rConnectorZ :: Bool -> Int
rConnectorZ = \case
  True -> 1
  False -> 0

connectorF :: Double -> Bool
connectorF = (/= 0)

rConnectorF :: Bool -> Double
rConnectorF = \case
  True -> 1.0
  False -> 0.0

unsatArithApp :: forall {m} ctx
  . (CtxConstraint ctx m)
  => (E ctx -> E ctx -> E ctx)
  -> String
  -> E ctx
  -> m (E ctx)
unsatArithApp mkE op x  = evalE x >>= \case
  Bottom t e0 es -> pure $ Bottom t e0 es
  ValZ a' -> (\env ->
    LambdaC (Z :-> Z) (Z,Just Z) env (mkVar @(E ctx) "x")
      (mkE (ValZ a') (FormulaApp (VarS Z "x")))) <$> getEnv
  ValF a' -> (\env ->
    LambdaC (F :-> F) (F,Just F) env (mkVar @(E ctx) "x")
      (mkE (ValF a') (FormulaApp (VarS F "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling '" <> op <> "'-expression. Unsupported argument: "
    <> show x


binOP :: forall {m} a b c d ctx
  . (CtxConstraint ctx m)
  => (Int -> Int -> a)
  -> (Double -> Double -> b)
  -> (Int -> Double -> c)
  -> (Double -> Int -> d)
  -> (a -> E ctx)
  -> (b -> E ctx)
  -> (c -> E ctx)
  -> (d -> E ctx)
  -> String
  -> E ctx
  -> E ctx
  -> m (E ctx)
binOP iia ddb idc did ae be ce de op a b = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure $ ae (iia a' b')
  (ValF a', ValF b') -> pure $ be (ddb a' b')
  (ValZ a', ValF b') -> pure $ ce (idc a' b')
  (ValF a', ValZ b') -> pure $ de (did a' b')
  (Bottom t e0 es, Bottom _ e1 es') -> pure $ Bottom t e0 (e1 : es <> es')
  (Bottom t e0 es, _)             -> pure $ Bottom t e0 es
  (_, Bottom t e1 es')            -> pure $ Bottom t e1 es'
  (a',b') -> throwError
    $ "Error on evaling '" <> op <> "'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'

binOPComp :: forall {m} ctx
  . (CtxConstraint ctx m)
  => (Int -> Int -> Bool)
  -> (Double -> Double -> Bool)
  -> String
  -> E ctx
  -> E ctx
  -> m (E ctx)
binOPComp iia ddb =
  binOP
    iia
    ddb
    (\a' b' -> fromIntegral a' `ddb` b')
    (\a' b' -> a' `ddb` fromIntegral b')
    ValB
    ValB
    ValB
    ValB

arithBuilder :: forall {m} ctx
  . (CtxConstraint ctx m)
  => (Int -> Int -> Int)
  -> (Double -> Double -> Double)
  -> String
  -> E ctx
  -> E ctx
  -> m (E ctx)
arithBuilder iia ddb = binOP
  iia
  ddb
  (\a' b' -> fromIntegral a' `ddb` b')
  (\a' b' -> a' `ddb` fromIntegral b')
  ValZ
  ValF
  ValF
  ValF

singleAppNum :: forall {m} a b ctx
  . (CtxConstraint ctx m)
  => (Int -> a)
  -> (Double -> b)
  -> (a -> E ctx)
  -> (b -> E ctx)
  -> String
  -> E ctx
  -> m (E ctx)
singleAppNum iai dbi ae be op a = evalE a >>= \case
  ValZ a' -> pure $ ae (iai a')
  ValF a' -> pure $ be (dbi a')
  Bottom t e0 es -> pure $ Bottom t e0 es
  a' -> throwError
    $ "Error on evaling '" <> op <> "'-expression. Unsupported argument: "
    <> show a'

trigBuilder :: forall {m} ctx
  . (CtxConstraint ctx m)
  => (Double -> Double)
  -> String
  -> E ctx
  -> m (E ctx)
trigBuilder f  = singleAppNum
  (f . fromIntegral)
  f
  ValF
  ValF
