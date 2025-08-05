{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# Language PatternSynonyms          #-}

{-|
Module      : Zilly.ADT.Expression
Description : Main Expression Tree a la Trees that grow for Zilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

Check
@@
@article{najd2016trees,
  title={Trees that grow},
  author={Najd, Shayan and Jones, Simon Peyton},
  journal={arXiv preprint arXiv:1610.04799},
  year={2016}
}
@@
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/trees-that-grow.pdf

-}
module Zilly.Puzzle.ADT.Expression where

import Zilly.Puzzle.Newtypes
import Zilly.Puzzle.Environment.TypedMap
import Data.Kind (Type)
import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Random
import Zilly.Puzzle.Effects.CC
import Zilly.Puzzle.Effects.Memoize
import Control.Monad.Error.Class
import Debug.Trace (trace)

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


{-| Zilly expression Language. |-}
data  E  (ctx :: Type) where
  ValZ      :: Int -> E ctx
  ValF      :: Double -> E ctx
  ValB      :: Bool -> E ctx
  ValS      :: String -> E ctx
  Var      :: LensM (E ctx) -> E ctx
  If       :: E ctx -> E ctx  -> E ctx -> E ctx
  Lambda   :: (Types,Maybe Types) -> LensM (E ctx) -> E ctx -> E ctx
  Defer    :: E ctx  -> E ctx
  -- Formula  :: LensM (E ctx) -> E ctx
  App      :: E ctx -> E ctx -> E ctx
  LambdaC  :: (Types, Maybe Types) -> TypeRepMap (E ctx) -> LensM (E ctx) -> E ctx  -> E ctx
  LazyC    :: TypeRepMap (E ctx) -> E ctx ->  Memoized (EvalMonad (E ctx)) (E ctx) -> E ctx
  MkTuple  :: E ctx -> E ctx -> [E ctx] -> E ctx
  Bottom   :: EvalError -> [EvalError] -> E ctx

type family LambdaCtx  (ctx :: Type) :: Type
type family LambdaCCtx (ctx :: Type) :: Type

data LambdaTag
data LambdaCTag

class HasArgType ctx tag where
  type ArgType ctx tag :: Type
  argType :: ArgType ctx tag -> Types

class HasRetType ctx tag where
  type RetType ctx tag :: Type
  retType :: RetType ctx tag -> Maybe Types



pattern VarS :: forall {m} ctx. (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m) => String -> E ctx
pattern VarS s <- Var (varNameM -> s) where
  VarS s = Var (mkVar @(E ctx) s)

pattern Formula :: forall {m} ctx. (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m) => E ctx
pattern Formula <- Var (varNameM -> "formula") where
  Formula  = Var (mkVar @(E ctx) "formula")

pattern Random :: forall {m} ctx. (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m) => E ctx
pattern Random <- Var (varNameM -> "random") where
  Random = Var (mkVar @(E ctx) "random")

pattern Head :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
pattern Head <- Var (varNameM -> "head") where
  Head = Var (mkVar @(E ctx) "head")

pattern Tail :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
pattern Tail <- Var (varNameM -> "tail") where
  Tail = Var (mkVar @(E ctx) "tail")


pattern MinusInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern MinusInfix a b <- App (App (Var (varNameM -> "-")) a) b where
  MinusInfix a b = App (App (Var (mkVar @(E ctx) "-")) a) b

pattern PlusInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern PlusInfix a b <- App (App (Var (varNameM -> "+")) a) b where
  PlusInfix a b = App (App (Var (mkVar @(E ctx) "+")) a) b

pattern TimesInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern TimesInfix a b <- App (App (Var (varNameM -> "*")) a) b where
  TimesInfix a b = App (App (Var (mkVar @(E ctx) "*")) a) b

pattern DivInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern DivInfix a b <- App (App (Var (varNameM -> "/")) a) b where
  DivInfix a b = App (App (Var (mkVar @(E ctx) "/")) a) b

pattern PowInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m )
  => E ctx -> E ctx -> E ctx
pattern PowInfix a b <- App (App (Var (varNameM -> "^")) a) b where
  PowInfix a b = App (App (Var (mkVar @(E ctx) "^")) a) b

pattern LTInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LTInfix a b <- App (App (Var (varNameM -> "<")) a) b where
  LTInfix a b = App (App (Var (mkVar @(E ctx) "<")) a) b

pattern LEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LEInfix a b <- App (App (Var (varNameM -> "<=")) a) b where
  LEInfix a b = App (App (Var (mkVar @(E ctx) "<=")) a) b

pattern GTInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GTInfix a b <- App (App (Var (varNameM -> ">")) a) b where
  GTInfix a b = App (App (Var (mkVar @(E ctx) ">")) a) b

pattern GEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GEInfix a b <- App (App (Var (varNameM -> ">=")) a) b where
  GEInfix a b = App (App (Var (mkVar @(E ctx) ">=")) a) b

pattern EQInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern EQInfix a b <- App (App (Var (varNameM -> "=")) a) b where
  EQInfix a b = App (App (Var (mkVar @(E ctx) "=")) a) b

pattern NEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern NEInfix a b <- App (App (Var (varNameM -> "<>")) a) b where
  NEInfix a b = App (App (Var (mkVar @(E ctx) "<>")) a) b

pattern AppendInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern AppendInfix a b <- App (App (Var (varNameM -> "++")) a) b where
  AppendInfix a b = App (App (Var (mkVar @(E ctx) "++")) a) b

pattern AndInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern AndInfix a b <- App (App (Var (varNameM -> "&&")) a) b where
  AndInfix a b = App (App (Var (mkVar @(E ctx) "&&")) a) b

pattern OrInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern OrInfix a b <- App (App (Var (varNameM -> "||")) a) b where
  OrInfix a b = App (App (Var (mkVar @(E ctx) "||")) a) b

pattern MinusSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern MinusSat a b <- App (App (Var (varNameM -> "-")) a) b where
  MinusSat a b = App (App (Var (mkVar @(E ctx) "-")) a) b

pattern PlusSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern PlusSat a b <- App (App (Var (varNameM -> "+")) a) b where
  PlusSat a b = App (App (Var (mkVar @(E ctx) "+")) a) b

pattern TimesSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern TimesSat a b <- App (App (Var (varNameM -> "*")) a) b where
  TimesSat a b = App (App (Var (mkVar @(E ctx) "*")) a) b

pattern DivSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern DivSat a b <- App (App (Var (varNameM -> "/")) a) b where
  DivSat a b = App (App (Var (mkVar @(E ctx) "/")) a) b

pattern PowSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern PowSat a b <- App (App (Var (varNameM -> "^")) a) b where
  PowSat a b = App (App (Var (mkVar @(E ctx) "^")) a) b

pattern AppendSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern AppendSat a b <- App (App (Var (varNameM -> "++")) a) b where
  AppendSat a b = App (App (Var (mkVar @(E ctx) "++")) a) b

pattern AndSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern AndSat a b <- App (App (Var (varNameM -> "&&")) a) b where
  AndSat a b = App (App (Var (mkVar @(E ctx) "&&")) a) b

pattern OrSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern OrSat a b <- App (App (Var (varNameM -> "||")) a) b where
  OrSat a b = App (App (Var (mkVar @(E ctx) "||")) a) b

pattern SubtractSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern SubtractSat a b <- App (App (Var (varNameM -> "-subtractSat")) a) b where
  SubtractSat a b = App (App (Var (mkVar @(E ctx) "-subtractSat")) a) b

pattern LTSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LTSat a b <- App (App (Var (varNameM -> "<")) a) b where
  LTSat a b = App (App (Var (mkVar @(E ctx) "<")) a) b

pattern LESat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LESat a b <- App (App (Var (varNameM -> "<=")) a) b where
  LESat a b = App (App (Var (mkVar @(E ctx) "<=")) a) b

pattern GTSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx

pattern GTSat a b <- App (App (Var (varNameM -> ">")) a) b where
  GTSat a b = App (App (Var (mkVar @(E ctx) ">")) a) b
pattern GESat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GESat a b <- App (App (Var (varNameM -> ">=")) a) b where
  GESat a b = App (App (Var (mkVar @(E ctx) ">=")) a) b

pattern EQSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern EQSat a b <- App (App (Var (varNameM -> "=")) a) b where
  EQSat a b = App (App (Var (mkVar @(E ctx) "=")) a) b

pattern NESat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern NESat a b <- App (App (Var (varNameM -> "<>")) a) b where
  NESat a b = App (App (Var (mkVar @(E ctx) "<>")) a) b

pattern MinusUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern MinusUnsat <- Var (varNameM -> "minus") where
  MinusUnsat = Var (mkVar @(E ctx) "minus")

pattern PlusUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern PlusUnsat <- Var (varNameM -> "plus") where
  PlusUnsat = Var (mkVar @(E ctx) "plus")
pattern TimesUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern TimesUnsat <- Var (varNameM -> "times") where
  TimesUnsat = Var (mkVar @(E ctx) "times")

pattern DivUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern DivUnsat <- Var (varNameM -> "div") where
  DivUnsat = Var (mkVar @(E ctx) "div")

pattern PowUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern PowUnsat <- Var (varNameM -> "pow") where
  PowUnsat = Var (mkVar @(E ctx) "pow")

pattern AppendUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern AppendUnsat <- Var (varNameM -> "append") where
  AppendUnsat = Var (mkVar @(E ctx) "append")

pattern AndUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern AndUnsat <- Var (varNameM -> "and") where
  AndUnsat = Var (mkVar @(E ctx) "and")

pattern OrUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern OrUnsat <- Var (varNameM -> "or") where
  OrUnsat = Var (mkVar @(E ctx) "or")

pattern SubtractUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern SubtractUnsat <- Var (varNameM -> "subtract") where
  SubtractUnsat = Var (mkVar @(E ctx) "subtract")

pattern LTSatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern LTSatUnsat <- Var (varNameM -> "lt") where
  LTSatUnsat = Var (mkVar @(E ctx) "lt")

pattern LESatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern LESatUnsat <- Var (varNameM -> "le") where
  LESatUnsat = Var (mkVar @(E ctx) "le")

pattern GTSatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern GTSatUnsat <- Var (varNameM -> "gt") where
  GTSatUnsat = Var (mkVar @(E ctx) "gt")

pattern GESatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern GESatUnsat <- Var (varNameM -> "ge") where
  GESatUnsat = Var (mkVar @(E ctx) "ge")

pattern EQSatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern EQSatUnsat <- Var (varNameM -> "eq") where
  EQSatUnsat = Var (mkVar @(E ctx) "eq")

pattern NESatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern NESatUnsat <- Var (varNameM -> "ne") where
  NESatUnsat = Var (mkVar @(E ctx) "ne")

pattern A_1 :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern A_1 a <- App (Var (varNameM -> "_1")) a where
  A_1 a = App (Var (mkVar @(E ctx) "_1")) a

pattern A_2 :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern A_2 a <- App (Var (varNameM -> "_2")) a where
  A_2 a = App (Var (mkVar @(E ctx) "_2")) a

pattern Negate :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Negate a <- App (Var (varNameM -> "negate")) a where
  Negate a = App (Var (mkVar @(E ctx) "negate")) a

pattern MinusU :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern MinusU a <- App (Var (varNameM -> "minusU")) a where
  MinusU a = App (Var (mkVar @(E ctx) "minusU")) a


pattern LogE :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern LogE a <- App (Var (varNameM -> "log")) a where
  LogE a = App (Var (mkVar @(E ctx) "log")) a


pattern Sin :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Sin a <- App (Var (varNameM -> "sin")) a where
  Sin a = App (Var (mkVar @(E ctx) "sin")) a

pattern Cos :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Cos a <- App (Var (varNameM -> "cos")) a where
  Cos a = App (Var (mkVar @(E ctx) "cos")) a

pattern Tan :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Tan a <- App (Var (varNameM -> "tan")) a where
  Tan a = App (Var (mkVar @(E ctx) "tan")) a


pattern ASin :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern ASin a <- App (Var (varNameM -> "asin")) a where
  ASin a = App (Var (mkVar @(E ctx) "asin")) a

pattern ACos :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern ACos a <- App (Var (varNameM -> "acos")) a where
  ACos a = App (Var (mkVar @(E ctx) "acos")) a

pattern ATan :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern ATan a <- App (Var (varNameM -> "atan")) a where
  ATan a = App (Var (mkVar @(E ctx) "atan")) a



data EvalError
  = FromGammaError GammaErrors
  | CustomError String


memoVal :: forall {m} ctx.
  ( CtxConstraint ctx m
  ) => E ctx -> m (Memoized m (E ctx))
memoVal  e = memoizeWithCC . evalE $ e

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
evalE (Lambda lctx arg body)
  = (\env -> LambdaC lctx env arg body) <$> getEnv
evalE (Defer a)   = do
  env <- getEnv
  ma <- memoizeWithCC $ withEnv env $ evalE a
  pure $ LazyC env a ma
evalE (App Formula (Var x)) = getEnv >>= viewM x
evalE (App Random x) = evalE x >>= \case
  Bottom e0 es   -> pure $ Bottom e0 es
  ValZ e' | e' < 1 -> pure $ ValZ 0
  ValZ e' -> randInt e' >>= pure . ValZ
  ValF e' | e' < 0 -> pure $ ValF 0.0
  ValF e' -> randFloat e' >>= pure . ValF
  e' -> throwError
    $ "Error on evaling 'random' expression. Unsupported argument: "
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
  (ValZ a', ValZ b') -> pure . ValB $ a' == b'
  (ValF a', ValF b') -> pure . ValB $ a' == b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' == b'
  (ValF a', ValZ b') -> pure . ValB $ a' == fromIntegral b'
  (ValB a', ValB b') -> pure . ValB $ a' == b'
  (ValS a', ValS b') -> pure . ValB $ a' == b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'eq'-expression. Unsupported arguments: "
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
    $ "Error on evaling 'ne'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (LTSat a b) = evalE $ LTInfix a b
evalE (LESat a b) = evalE $ LEInfix a b
evalE (GTSat a b) = evalE $ GTInfix a b
evalE (GESat a b) = evalE $ GEInfix a b
evalE (EQSat a b) = evalE $ EQInfix a b
evalE (NESat a b) = evalE $ NEInfix a b
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
evalE (MinusSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' - b'
  (ValF a', ValF b') -> pure . ValF $ a' - b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' - b'
  (ValF a', ValZ b') -> pure . ValF $ a' - fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'minusSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (PlusSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' + b'
  (ValF a', ValF b') -> pure . ValF $ a' + b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' + b'
  (ValF a', ValZ b') -> pure . ValF $ a' + fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'plusSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (TimesSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' * b'
  (ValF a', ValF b') -> pure . ValF $ a' * b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' * b'
  (ValF a', ValZ b') -> pure . ValF $ a' * fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'timesSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (DivSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> if b' == 0
    then throwError "Error on evaling 'divSat'-expression. Division by zero."
    else pure . ValF $ fromIntegral a' / fromIntegral b'
  (ValF a', ValF b') -> if b' == 0.0
    then throwError "Error on evaling 'divSat'-expression. Division by zero."
    else pure . ValF $ a' / b'
  (ValZ a', ValF b') -> if b' == 0.0
    then throwError "Error on evaling 'divSat'-expression. Division by zero."
    else pure . ValF $ fromIntegral a' / b'
  (ValF a', ValZ b') -> if b' == 0
    then throwError "Error on evaling 'divSat'-expression. Division by zero."
    else pure . ValF $ a' / fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'divSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (PowSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValZ $ a' ^ b'
  (ValF a', ValF b') -> pure . ValF $ a' ** b'
  (ValZ a', ValF b') -> pure . ValF $ fromIntegral a' ** b'
  (ValF a', ValZ b') -> pure . ValF $ a' ** fromIntegral b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'powSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
evalE (AppendSat a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValS a', ValS b') -> pure . ValS $ a' <> b'
  (ValZ a', ValZ b') -> pure . ValS $ show a' <> show b'
  (ValF a', ValF b') -> pure . ValS $ show a' <> show b'
  (ValZ a', ValF b') -> pure . ValS $ show a' <> show b'
  (ValF a', ValZ b') -> pure . ValS $ show a' <> show b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling 'appendSat'-expression. Unsupported arguments: "
    <> show a' <> " and " <> show b'
-- evalE (AndSat a b) = evalE $ AndInfix a b
-- evalE (OrSat a b) = evalE $ OrInfix a b
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
evalE (EQInfix a b) = (,) <$> evalE a <*> evalE b >>= \case
  (ValZ a', ValZ b') -> pure . ValB $ a' == b'
  (ValF a', ValF b') -> pure . ValB $ a' == b'
  (ValZ a', ValF b') -> pure . ValB $ fromIntegral a' == b'
  (ValF a', ValZ b') -> pure . ValB $ a' == fromIntegral b'
  (ValB a', ValB b') -> pure . ValB $ a' == b'
  (ValS a', ValS b') -> pure . ValB $ a' == b'
  (Bottom e0 es, Bottom e1 es') -> pure $ Bottom e0 (e1 : es <> es')
  (Bottom e0 es, _)             -> pure $ Bottom e0 es
  (_, Bottom e1 es')            -> pure $ Bottom e1 es'
  (a',b') -> throwError
    $ "Error on evaling '='-expression. Unsupported arguments: "
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
evalE (LazyC _ e mem)  = runMemoized mem
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
--
-- cTrue :: E m PZ
-- cTrue = Val  (rConnector True)
--
-- cFalse :: E m PZ
-- cFalse = Val (rConnector False)
--
infixl 1 $$

($$) :: E ctx -> E ctx -> E ctx
($$) = App

uminusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
uminusStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ MinusU (Formula $$ VarS "x")

negateStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
negateStd
  = Lambda (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Negate (Formula $$ VarS "x")

subStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
subStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ MinusInfix (Formula $$ VarS "y") (Formula $$ (VarS "x"))


minusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
minusStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ MinusInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

plusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
plusStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ PlusInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

timesStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
timesStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ TimesInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

divStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
divStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ DivInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

powStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
powStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ PowInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

appendStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
appendStd
  = Lambda (ZString, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (ZString, Nothing) (mkVar @(E ctx) "y")
  $ AppendInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

andStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
andStd
  = Lambda (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (ZBool, Nothing) (mkVar @(E ctx) "y")
  $ AndInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

orStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
orStd
  = Lambda (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (ZBool, Nothing) (mkVar @(E ctx) "y")
  $ OrInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

ltStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
ltStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ LTInfix (Formula $$ VarS "y") (Formula $$ (VarS "x"))

leStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
leStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ LEInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

gtStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
gtStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ GTInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

geStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
geStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ GEInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

eqStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
eqStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ EQInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

neStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
neStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ NEInfix (Formula $$ VarS "x") (Formula $$ (VarS "y"))

eStd :: E ctx
eStd = ValF 2.718281828459045


newtype UT = UT String

instance Show UT where
  show (UT s) = s
--
-- --------------------------
-- -- Show instance
-- --------------------------
--
-- showRuntimeError :: GammaErrors -> String
-- showRuntimeError ((TypeMismatch s (ExpectedType e) (ActualType t))) = concat
--   [ "Variable type Mismatch: " <> show s
--   , ". Expected type: " <> show e
--   , " But got instead: " <> show t
--   ]
-- showRuntimeError ((VariableNotDefined s))
--   = "Variable not defined: " <> show s
-- showRuntimeError ((VariableAlreadyDeclared s))
--   = "Trying to declare an already existing variable: " <> show s
-- showRuntimeError ((VariableNotInitialized s))
--   = "Trying to use a variable that hasnt been initialized: " <> show s
--
--
instance
  ( CtxPureConstraint ctx
  , MonadIO (EvalMonad (E ctx))
  , MonadError String (EvalMonad (E ctx))
  ) => Show (E ctx) where
  showsPrec p = \case
    ValZ n -> showString (show n)
    ValF n -> showString (show n)
    ValB s -> showString (show s)
    ValS s -> showString (show s)
    Var  x -> showsPrec p . UT . varNameM $ x
    If  c t f -> showParen (p > 10) $ showString "if( " . shows c . showString ", " . shows t . showString ", " . shows f . showString ")"
    Lambda (at,mt)  x t ->  showParen (p > 9)
      $ showString "λ("
      . shows at
      . showString " "
      . shows (UT $ varNameM  x)
      . showString ")"
      . showString (maybe ""  (mappend " => " . show) $ mt)
      . showString " -> " .  showsPrec 0 t
    LambdaC (at,mt) _ x t -> showParen (p > 9)
      $  showString "λ( "
      . shows at
      . showString " "
      . shows (UT $ varNameM  x)
      . showString ")"
      . showString (maybe "" (mappend " => " . show) $ mt)
      . showString " -> " .  showsPrec 0 t
    MinusInfix a b
      -> showParen (p > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
    PlusInfix a b
      -> showParen (p > 6) $ showsPrec 6 a . showString " + " . showsPrec 7 b
    TimesInfix a b
      -> showParen (p > 7) $ showsPrec 7 a . showString " * " . showsPrec 8 b
    DivInfix a b
      -> showParen (p > 7) $ showsPrec 7 a . showString " / " . showsPrec 8 b
    PowInfix a b
      -> showParen (p > 8) $ showsPrec 9 a . showString " ^ " . showsPrec 8 b
    AppendInfix a b
      -> showParen (p > 6) $ showsPrec 6 a . showString " ++ " . showsPrec 7 b
    AndInfix a b
      -> showParen (p > 3) $ showsPrec 4 a . showString " && " . showsPrec 3 b
    OrInfix a b
      -> showParen (p > 3) $ showsPrec 4 a . showString " || " . showsPrec 3 b
    SubtractSat a b
      -> showParen (p > 6) $ showsPrec 6 b . showString " - " . showsPrec 7 a
    LTInfix a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " < " . showsPrec 5 b
    LEInfix a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " <= " . showsPrec 5 b
    GTInfix a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " > " . showsPrec 5 b
    GEInfix a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " >= " . showsPrec 5 b
    EQInfix a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " = " . showsPrec 5 b
    NEInfix a b
      -> showParen (p > 4) $ showsPrec 4 a . showString " <> " . showsPrec 5 b
    Negate a -> showParen (p > 11) $ showString "~" . showsPrec 11 a
    MinusU a -> showParen (p > 11) $ showString "-" . showsPrec 11 a



    App  f a -> showParen (p > 10) $ showsPrec 10 f . showChar '(' . shows a . showChar ')'
    Defer  v -> showString "'" . showsPrec 11 v . showString "'"
    LazyC _ e _ -> showsPrec p e -- showChar '<' . showsPrec 10 e . showString  ", " . showsPrec 10 env . showChar '>'
    -- Formula  e -> showString "formula(" . (shows . UT . varNameM) e . showChar ')'
    -- Subtyped  e ->  showsPrec p e --showString "@@" . showsPrec p e
    -- Minus a b  -> showString "_minus(" . shows a . showString ")(" . shows b . showString ")"
    -- Less  a b  -> showString "_lt(" . shows a . showString ")(" . shows b . showString ")"
    -- Minus  a b -> showParen (p > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
    -- Less  a b -> showParen (p > 10) $ showsPrec 4 a . showString " < " . showsPrec 5 b
    -- Random a  -> showString "_random(" . shows a . showChar ')'
    Bottom _ _-> showString "⊥"
    MkTuple a b xs -> showString "(" . shows a . showString ", " . shows b . showString ")"
    -- FstT a -> showString "fst(" . shows a . showString ")"
    -- SndT a -> showString "snd(" . shows a . showString ")"
