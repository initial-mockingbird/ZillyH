{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Zilly.Puzzle.Expression.Interpreter
  ( Effects
  , CtxConstraint
  , CtxPureConstraint
  , memoVal
  , evalE
  , InterpretMode (..)
  , evalEClassic
  ) where


import Zilly.Puzzle.Types.Exports
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Expression.Patterns
import Zilly.Puzzle.Expression.Classes
import Zilly.Puzzle.Expression.Show ()
import Zilly.Puzzle.Expression.Eq ()
import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Random
import Zilly.Puzzle.Effects.CC
import Zilly.Puzzle.Effects.Memoize
import Control.Monad.Error.Class
import Data.Array
import Data.Traversable

data InterpretMode = ClassicInterpreter |  UnsugaredInterpreter deriving Eq




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
fetchExpression (Var l) = getEnv >>= getL l >>= fetchExpression
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
evalE   (Var l  )  = getEnv >>= getL l >>= evalE
evalE (If c a b) = do
  mc' <- evalE c
  case mc' of
    Bottom e0 es -> pure $ Bottom e0 es
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
evalE (MkArray es) = MkArray <$> traverse evalE es
evalE (Lambda lctx arg body) = (\env -> LambdaC lctx env arg body) <$> getEnv
evalE (Defer a)   = do
  env <- getEnv
  ma <- memoizeWithCC $ withEnv env $ evalE a
  pure $ LazyC env a ma
evalE (ArraySlice earr eixs) = do
  ixs <- for eixs $ \(l,u) -> (,) <$> evalE @ctx l <*> traverse (evalE @ctx) u >>= \case
    (ValZ l', Just (ValZ u')) -> pure (l', Just u')
    (ValZ l', Nothing) -> pure (l', Nothing)
    (a',b') -> throwError
      $ "Error on evaling 'arraySlice' expression. Unsupported index: "
      <> show a' <> " and " <> show b'
  arr <- fetchExpression earr >>= \case
    MkArray es' -> pure  es'
    e' -> evalE e' >>= \case
      MkArray es'' -> pure es''
      e'' -> throwError
        $ "Error on evaling 'arraySlice' expression. Unsupported array: "
        <> show e''
  farr <- traverse (evalE @ctx) (slice' ixs arr)
  case shapeL farr of
    [] -> pure $ unScalar farr
    _  -> pure $ MkArray farr
evalE (App Formula (Var x)) = getEnv >>= viewM x
evalE (App Formula (ArraySlice earr eixs)) = do
  ixs <- for eixs $ \(l,u) -> (,) <$> evalE @ctx l <*> traverse (evalE @ctx) u >>= \case
    (ValZ l', Just (ValZ u')) -> pure (l', Just u')
    (ValZ l', Nothing) -> pure (l', Nothing)
    (a',b') -> throwError
      $ "Error on evaling 'arraySlice' expression. Unsupported index: "
      <> show a' <> " and " <> show b'
  fetchExpression earr >>= evalE . App Formula >>=  \case
    MkArray arr -> do
      let farr = slice' ixs arr
      case shapeL farr of
        [] -> pure $ unScalar farr
        _  -> pure $ MkArray farr
    e' -> pure $ ArraySlice e' $ (\(a,b) -> (ValZ a, ValZ <$> b)) <$> ixs
evalE (App Formula e) = pure e
evalE (App Random x) = evalE x >>= \case
  Bottom e0 es   -> pure $ Bottom e0 es
  ValZ e' | e' < 1 -> pure $ ValZ 0
  ValZ e' -> ValZ <$> randInt e'
  ValF e' | e' < 0 -> pure $ ValF 0.0
  ValF e' -> ValF <$> randFloat e'
  e' -> throwError
    $ "Error on evaling 'random' expression. Unsupported argument: "
    <> show e'
evalE (Dim e) = evalE e >>= \case
  MkArray es -> pure . MkArray . (\xs -> Data.Array.fromList [length xs] xs)  . fmap ValZ . shapeL $ es
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'dim' expression. Unsupported argument: "
    <> show e'
evalE (Length e) = evalE e >>= \case
  MkArray es -> pure . ValZ . size $  es
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'length' expression. Unsupported argument: "
    <> show e'
evalE (MatrixSat r c f) = (,) <$> evalE r <*> evalE c >>= \case
  (ValZ r', ValZ c') | r' > 0 && c' > 0 -> do
    f' <- evalE f
    xs <- traverse evalE
      [ (f' $$ ValZ x) $$ ValZ y | x <- [0..r'-1], y <- [0..c'-1]]
    pure $ MkArray $ Data.Array.fromList [r', c'] xs
  (ValZ r', ValZ c') -> throwError
    $ "Error on evaling 'matrix' expression. Invalid dimensions: "
    <> show r' <> " and " <> show c'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'matrix' expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (VectorSat r f) = evalE r >>= \case
  ValZ r' | r' > 0 -> do
    f' <- evalE f
    xs <- traverse evalE [App f' (ValZ x) | x <- [0..r'-1]]
    pure $ MkArray $ Data.Array.fromList [r'] xs
  ValZ r' -> throwError
    $ "Error on evaling 'vector' expression. Invalid dimension: "
    <> show r'
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'vector' expression. Unsupported argument: "
    <> show e'
evalE (ConsSat h t) = (,) <$> evalE h <*> evalE t >>= \case
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (h', MkArray t')              -> pure $ MkArray $ append (Data.Array.fromList [1] [h']) t'
  (_,e') -> throwError
    $ "Error on evaling 'cons' expression. Unsupported tail: "
    <> show e'
evalE (LTInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' < b'
  (ValF a', ValF b') -> pure . ValB $ a' < b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' < b'
  (ValF a', ValZ b') -> pure . ValB $ a' < fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'lt'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (LEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' <= b'
  (ValF a', ValF b') -> pure . ValB $ a' <= b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' <= b'
  (ValF a', ValZ b') -> pure . ValB $ a' <= fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'lt'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (GTInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' > b'
  (ValF a', ValF b') -> pure . ValB $ a' > b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' > b'
  (ValF a', ValZ b') -> pure . ValB $ a' > fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'gt'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (GEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' >= b'
  (ValF a', ValF b') -> pure . ValB $ a' >= b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' >= b'
  (ValF a', ValZ b') -> pure . ValB $ a' >= fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'ge'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (EQInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (a',b') -> pure . ValB $ a' == b'
evalE (NEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (a',b') -> pure . ValB $ a' /= b'
evalE (LogE a) = evalE a >>= \case
  ValZ a' | a' <= 0 -> throwError "Error on evaling 'log'-expression. Logarithm of zero or negative number."
  ValF a' | a' <= 0 -> throwError "Error on evaling 'log'-expression. Logarithm of zero or negative number."
  ValZ a'           -> pure . ValF $ log (fromIntegral a')
  ValF a'           -> pure . ValF $ log a'
  Bottom e0 es      -> pure $ Bottom e0 es
  e'                -> throwError
    $ "Error on evaling 'log'-expression. Unsupported argument: "
    <> show e'
evalE (Sin a) = evalE a >>= \case
  ValZ a' -> pure . ValF $ sin (fromIntegral a')
  ValF a' -> pure . ValF $ sin a'
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'sin'-expression. Unsupported argument: "
    <> show e'
evalE (Cos a) = evalE a >>= \case
  ValZ a' -> pure . ValF $ cos (fromIntegral a')
  ValF a' -> pure . ValF $ cos a'
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'cos'-expression. Unsupported argument: "
    <> show e'
evalE (Tan a) = evalE a >>= \case
  ValZ a' -> pure . ValF $ tan (fromIntegral a')
  ValF a' -> pure . ValF $ tan a'
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'tan'-expression. Unsupported argument: "
    <> show e'
evalE (ASin a) = evalE a >>= \case
  -- ValZ a' | abs a' > 1 -> throwError "Error on evaling 'asin'-expression. Argument out of range."
  -- ValF a' | abs a' > 1 -> throwError "Error on evaling 'asin'-expression. Argument out of range."
  ValZ a'              -> pure . ValF $ asin (fromIntegral a')
  ValF a'              -> pure . ValF $ asin a'
  Bottom e0 es         -> pure $ Bottom e0 es
  e'                   -> throwError
    $ "Error on evaling 'asin'-expression. Unsupported argument: "
    <> show e'
evalE (ACos a) = evalE a >>= \case
  -- ValZ a' | abs a' > 1 -> throwError "Error on evaling 'acos'-expression. Argument out of range."
  -- ValF a' | abs a' > 1 -> throwError "Error on evaling 'acos'-expression. Argument out of range."
  ValZ a'              -> pure . ValF $ acos (fromIntegral a')
  ValF a'              -> pure . ValF $ acos a'
  Bottom e0 es         -> pure $ Bottom e0 es
  e'                   -> throwError
    $ "Error on evaling 'acos'-expression. Unsupported argument: "
    <> show e'
evalE (ATan a) = evalE a >>= \case
  ValZ a' -> pure . ValF $ atan (fromIntegral a')
  ValF a' -> pure . ValF $ atan a'
  Bottom e0 es -> pure $ Bottom e0 es
  e' -> throwError
    $ "Error on evaling 'atan'-expression. Unsupported argument: "
    <> show e'
evalE (SubtractSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ b' - a'
  (ValF a', ValF b') -> pure . ValF $ b' - a'
  (ValZ a', ValF b') -> pure . ValF $ b' - fromIntegral a'
  (ValF a', ValZ b') -> pure . ValF $ fromIntegral b' - a'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'subtractSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (MinusInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' - b'
  (ValF a', ValF b') -> pure . ValF $ a' - b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' - b'
  (ValF a', ValZ b') -> pure . ValF $ a' - fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '-'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (PlusInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' + b'
  (ValF a', ValF b') -> pure . ValF $ a' + b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' + b'
  (ValF a', ValZ b') -> pure . ValF $ a' + fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '+''-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (TimesInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' * b'
  (ValF a', ValF b') -> pure . ValF $ a' * b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' * b'
  (ValF a', ValZ b') -> pure . ValF $ a' * fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '*'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
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
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '/'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (PowInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' ^ b'
  (ValF a', ValF b') -> pure . ValF $ a' ** b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' ** b'
  (ValF a', ValZ b') -> pure . ValF $ a' ** fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '^'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (LTInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' < b'
  (ValF a', ValF b') -> pure . ValB $ a' < b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' < b'
  (ValF a', ValZ b') -> pure . ValB $ a' < fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '<'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (LEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' <= b'
  (ValF a', ValF b') -> pure . ValB $ a' <= b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' <= b'
  (ValF a', ValZ b') -> pure . ValB $ a' <= fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '<='-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (GTInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' > b'
  (ValF a', ValF b') -> pure . ValB $ a' > b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' > b'
  (ValF a', ValZ b') -> pure . ValB $ a' > fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '>'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (GEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' >= b'
  (ValF a', ValF b') -> pure . ValB $ a' >= b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' >= b'
  (ValF a', ValZ b') -> pure . ValB $ a' >= fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '>='-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (NEInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' /= b'
  (ValF a', ValF b') -> pure . ValB $ a' /= b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' /= b'
  (ValF a', ValZ b') -> pure . ValB $ a' /= fromIntegral b'
  (ValB a', ValB b') -> pure . ValB $ a' /= b'
  (ValS a', ValS b') -> pure . ValB $ a' /= b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '<>'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (AppendInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValS a', ValS b') -> pure . ValS $ a' <> b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '++'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (AndInfix a b) = evalE a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValB True -> evalE b >>= \case
    Bottom e1 es' -> pure $ Bottom e1 es'
    ValB b' -> pure . ValB $ b'
    b' -> throwError
      $ "Error on evaling '&&'-expression. Unsupported right argument: "
      <> show b'
  ValB False -> pure $ ValB False
  a' -> throwError
    $ "Error on evaling '&&'-expression. Unsupported left argument: "
    <> show a'
evalE (OrInfix a b) = evalE a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValB True -> pure $ ValB True
  ValB False -> evalE b >>= \case
    Bottom e1 es' -> pure $ Bottom e1 es'
    ValB b' -> pure . ValB $ b'
    b' -> throwError
      $ "Error on evaling '||'-expression. Unsupported right argument: "
      <> show b'
  a' -> throwError
    $ "Error on evaling '||'-expression. Unsupported left argument: "
    <> show a'
evalE (Negate a) = evalE a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValB a' -> pure . ValB $ not a'
  x' -> throwError
    $ "Error on evaling 'negate'-expression. Unsupported argument: "
    <> show x'
evalE (MinusU a) = evalE a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> pure . ValZ $ -a'
  ValF a' -> pure . ValF $ -a'
  x' -> throwError
    $ "Error on evaling 'minusU'-expression. Unsupported argument: "
    <> show x'
evalE (App Head x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValS [] -> pure $ ValS ""
  ValS (h:_) -> pure . ValS . pure $ h
  x' -> throwError
    $ "Error on evaling 'head'-expression. Non string argument: "
    <> show x'
evalE (App Tail x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValS [] -> pure $ ValS ""
  ValS (_:xs) -> pure . ValS $ xs
  x' -> throwError
    $ "Error on evaling 'tail'-expression. Non string argument: "
    <> show x'
evalE (App MinusUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> (\env -> LambdaC (Z,Just Z) env (mkVar @(E ctx) "x") (MinusInfix (ValZ a') (App Formula (VarS "x")))) <$> getEnv
  ValF a' -> (\env -> LambdaC (F,Just F) env (mkVar @(E ctx) "x") (MinusInfix (ValF a') (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'minusUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App PlusUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> (\env -> LambdaC (Z,Just Z) env (mkVar @(E ctx) "x") (PlusInfix (ValZ a') (App Formula (VarS "x")))) <$> getEnv
  ValF a' -> (\env -> LambdaC (F,Just F) env (mkVar @(E ctx) "x") (PlusInfix (ValF a') (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'plusUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App TimesUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> (\env -> LambdaC (Z,Just Z) env (mkVar @(E ctx) "x") (TimesInfix (ValZ a') (App Formula (VarS "x")))) <$> getEnv
  ValF a' -> (\env -> LambdaC (F,Just F) env (mkVar @(E ctx) "x") (TimesInfix (ValF a') (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'timesUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App DivUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> (\env -> LambdaC (Z,Just Z) env (mkVar @(E ctx) "x") (DivInfix (ValZ a') (App Formula (VarS "x")))) <$> getEnv
  ValF a' -> (\env -> LambdaC (F,Just F) env (mkVar @(E ctx) "x") (DivInfix (ValF a') (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'divUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App PowUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> (\env -> LambdaC (Z,Just Z) env (mkVar @(E ctx) "x") (PowInfix (ValZ a') (App Formula (VarS "x")))) <$> getEnv
  ValF a' -> (\env -> LambdaC (F,Just F) env (mkVar @(E ctx) "x") (PowInfix (ValF a') (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'powUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App AppendUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValS a' -> (\env -> LambdaC (ZString,Just ZString) env (mkVar @(E ctx) "x") (AppendInfix (ValS a') (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'appendUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App AndUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValB b -> (\env -> LambdaC (ZBool,Just ZBool) env (mkVar @(E ctx) "x") (AndInfix (ValB b) (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'andUnsat'-expression. Unsupported argument: "
    <> show x
evalE (App OrUnsat x) = evalE x >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValB b -> (\env -> LambdaC (ZBool,Just ZBool) env (mkVar @(E ctx) "x") (OrInfix (ValB b) (App Formula (VarS "x")))) <$> getEnv
  _ -> throwError
    $ "Error on evaling 'orUnsat'-expression. Unsupported argument: "
    <> show x
evalE (A_1 a) = evalE a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  MkTuple a' _ _ -> pure $ a'
  _ -> throwError
    $ "Error on evaling 'A_1'-expression. Unsupported argument: "
    <> show a
evalE (A_2 a) = evalE a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  MkTuple _ b' _ -> pure $ b'
  _ -> throwError
    $ "Error on evaling 'A_2'-expression. Unsupported argument: "
    <> show a
evalE f@(LambdaC {}) = pure $ f
evalE (LazyC _ _ mem)  = runMemoized mem
evalE b@(Bottom {})  = pure $ b
evalE (MkTuple a b xs) = do
  a' <- evalE a
  b' <- evalE b
  xs' <- traverse evalE xs
  pure $ MkTuple a' b' xs'
evalE (App f x) = do
  mf' <- evalE f
  mx' <- evalE x
  case (mf',mx') of
    (Bottom e0 es, Bottom e1 es') -> pure  $ Bottom e0 (e1 : es <> es')
    (Bottom e0 es, _)             -> pure  $ Bottom e0 es
    (_, Bottom e1 es')            -> pure  $ Bottom e1 es'
    (LambdaC (t,_) env binded body,_)
      -> setFreshL binded env mx' t >>= \env' -> withEnv env' $ evalE body
    (Lambda (t,_) arg body, _)
      -> getEnv >>= \env -> setFreshL arg env mx' t >>= \env' -> withEnv env' $ evalE body

    _ -> error "Error on evaling 'function application'-expression. Function values can only be closures, subtyped functions, or bottom after reduction."

evalEClassic :: forall {m} ctx.
  ( CtxConstraint ctx m
  )
  => E ctx -> m (E ctx)
evalEClassic e@(ValZ {})   = pure e
evalEClassic   (Var l )    = getEnv >>= getL l >>= evalEClassic
evalEClassic (If c a b)  = do
  mc' <- evalEClassic c
  case mc' of
    Bottom e0 es -> pure $ Bottom e0 es
    ValZ c' ->
      case connectorZ c' of
        True  -> evalEClassic a
        False -> evalEClassic b
    _ -> throwError
      $ "Error on evaling 'if'-expression. Invalid condition: "
      <> show mc'
evalEClassic (Lambda lctx arg body) = (\env -> LambdaC lctx env arg body) <$> getEnv
evalEClassic (Defer a)  = do
  env <- getEnv
  ma <- memoizeWithCC $ withEnv env $ evalEClassic a
  pure $ LazyC env a ma
evalEClassic (App Formula (Var x)) = getEnv >>= viewM x
evalEClassic (App Random x) =  evalEClassic x >>= \case
  Bottom e0 es   -> pure $ Bottom e0 es
  ValZ e' | e' < 1 -> pure $ ValZ 0
  ValZ e' -> ValZ <$> randInt e'
  e' -> throwError
    $ "Error on evaling 'random' expression. Unsupported argument: "
    <> show e'
evalEClassic (LTInfix a b) = (,) <$> evalEClassic a <*> evalEClassic b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ . rConnectorZ  $ a' < b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'lt'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalEClassic (SubtractSat a b) = (,) <$> evalEClassic a <*> evalEClassic b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ b' - a'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'subtractSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalEClassic (MinusU a) = evalEClassic a >>= \case
  Bottom e0 es -> pure $ Bottom e0 es
  ValZ a' -> pure . ValZ $ -a'
  x' -> throwError
    $ "Error on evaling 'minusU'-expression. Unsupported argument: "
    <> show x'
evalEClassic f@(LambdaC {}) = pure $ f
evalEClassic (LazyC _ _ mem)  = runMemoized mem
evalEClassic b@(Bottom {})  = pure $ b
evalEClassic (MinusInfix a b) = (,) <$> evalEClassic a <*> evalEClassic b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' - b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '-'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalEClassic (App f x) = do
  mf' <- evalEClassic f
  mx' <- evalEClassic x
  case (mf',mx') of
    (Bottom e0 es, Bottom e1 es') -> pure  $ Bottom e0 (e1 : es <> es')
    (Bottom e0 es, _)             -> pure  $ Bottom e0 es
    (_, Bottom e1 es')            -> pure  $ Bottom e1 es'
    (LambdaC (t,_) env binded body,_)
      -> setFreshL binded env mx' t >>= \env' -> withEnv env' $ evalEClassic body
    (Lambda (t,_) arg body, _)
      -> getEnv >>= \env -> setFreshL arg env mx' t >>= \env' -> withEnv env' $ evalEClassic body

    _ -> error "Error on evaling 'function application'-expression. Function values can only be closures, subtyped functions, or bottom after reduction."
evalEClassic e = throwError
  $ "Runtime error: Unsupported expression in Zilly: "
  <> show e





-- --------------------------
-- -- Aux Functions
-- --------------------------
--
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
