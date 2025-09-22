{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TypeOperators         #-}

module Zilly.Puzzle.Expression.Patterns
  ( pattern VarS
  , pattern Formula
  , pattern Random
  , pattern Head
  , pattern Tail
  , pattern MinusInfix
  , pattern MinusInfix'
  , pattern PlusInfix
  , pattern PlusInfix'
  , pattern TimesInfix
  , pattern TimesInfix'
  , pattern DivInfix
  , pattern DivInfix'
  , pattern PowInfix
  , pattern PowInfix'
  , pattern LTInfix
  , pattern LTInfix'
  , pattern LEInfix
  , pattern LEInfix'
  , pattern GTInfix
  , pattern GTInfix'
  , pattern GEInfix
  , pattern GEInfix'
  , pattern EQInfix
  , pattern EQInfix'
  , pattern NEInfix
  , pattern NEInfix'
  , pattern AppendInfix
  , pattern AppendInfix'
  , pattern AndInfix
  , pattern AndInfix'
  , pattern OrInfix
  , pattern OrInfix'
  , pattern SubtractSat
  , pattern SubtractSat'
  , pattern MinusUnsat
  , pattern PlusUnsat
  , pattern TimesUnsat
  , pattern DivUnsat
  , pattern PowUnsat
  , pattern AppendUnsat
  , pattern AndUnsat
  , pattern OrUnsat
  , pattern SubtractUnsat
  , pattern LTSatUnsat
  , pattern LESatUnsat
  , pattern GTSatUnsat
  , pattern GESatUnsat
  , pattern EQSatUnsat
  , pattern NESatUnsat
  , pattern A_1
  , pattern A_2
  , pattern Negate
  , pattern Negate'
  , pattern MinusU
  , pattern MinusU'
  , pattern LogE
  , pattern Sin
  , pattern Cos
  , pattern Tan
  , pattern ASin
  , pattern ACos
  , pattern ATan
  , pattern Dim
  , pattern MatrixSat
  , pattern VectorSat
  , pattern ConsSat
  , pattern Length
  , ($$)
  ) where

import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Environment.TypedMap
import Control.Monad.IO.Class
import Control.Monad.Error.Class

infixl 1 $$

($$) :: E ctx -> E ctx -> E ctx
($$) = App


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

pattern MinusInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern MinusInfix' a b <- App (App (Var (varNameM -> "-")) a) b


pattern PlusInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern PlusInfix a b <- App (App (Var (varNameM -> "+")) a) b where
  PlusInfix a b = App (App (Var (mkVar @(E ctx) "+")) a) b

pattern PlusInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern PlusInfix' a b <- App (App (Var (varNameM -> "+")) a) b

pattern TimesInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern TimesInfix a b <- App (App (Var (varNameM -> "*")) a) b where
  TimesInfix a b = App (App (Var (mkVar @(E ctx) "*")) a) b

pattern TimesInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern TimesInfix' a b <- App (App (Var (varNameM -> "*")) a) b


pattern DivInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern DivInfix a b <- App (App (Var (varNameM -> "/")) a) b where
  DivInfix a b = App (App (Var (mkVar @(E ctx) "/")) a) b

pattern DivInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern DivInfix' a b <- App (App (Var (varNameM -> "/")) a) b


pattern PowInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m )
  => E ctx -> E ctx -> E ctx
pattern PowInfix a b <- App (App (Var (varNameM -> "^")) a) b where
  PowInfix a b = App (App (Var (mkVar @(E ctx) "^")) a) b

pattern PowInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern PowInfix' a b <- App (App (Var (varNameM -> "^")) a) b

pattern LTInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LTInfix a b <- App (App (Var (varNameM -> "<")) a) b where
  LTInfix a b = App (App (Var (mkVar @(E ctx) "<")) a) b

pattern LTInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern LTInfix' a b <- App (App (Var (varNameM -> "<")) a) b

pattern LEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LEInfix a b <- App (App (Var (varNameM -> "<=")) a) b where
  LEInfix a b = App (App (Var (mkVar @(E ctx) "<=")) a) b

pattern LEInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern LEInfix' a b <- App (App (Var (varNameM -> "<=")) a) b

pattern GTInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GTInfix a b <- App (App (Var (varNameM -> ">")) a) b where
  GTInfix a b = App (App (Var (mkVar @(E ctx) ">")) a) b

pattern GTInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern GTInfix' a b <- App (App (Var (varNameM -> ">")) a) b

pattern GEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GEInfix a b <- App (App (Var (varNameM -> ">=")) a) b where
  GEInfix a b = App (App (Var (mkVar @(E ctx) ">=")) a) b

pattern GEInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern GEInfix' a b <- App (App (Var (varNameM -> ">=")) a) b

pattern EQInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern EQInfix a b <- App (App (Var (varNameM -> "=")) a) b where
  EQInfix a b = App (App (Var (mkVar @(E ctx) "=")) a) b

pattern EQInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern EQInfix' a b <- App (App (Var (varNameM -> "=")) a) b

pattern NEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern NEInfix a b <- App (App (Var (varNameM -> "<>")) a) b where
  NEInfix a b = App (App (Var (mkVar @(E ctx) "<>")) a) b

pattern NEInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern NEInfix' a b <- App (App (Var (varNameM -> "<>")) a) b

pattern AppendInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern AppendInfix a b <- App (App (Var (varNameM -> "++")) a) b where
  AppendInfix a b = App (App (Var (mkVar @(E ctx) "++")) a) b

pattern AppendInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern AppendInfix' a b <- App (App (Var (varNameM -> "++")) a) b

pattern AndInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern AndInfix a b <- App (App (Var (varNameM -> "&&")) a) b where
  AndInfix a b = App (App (Var (mkVar @(E ctx) "&&")) a) b

pattern AndInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern AndInfix' a b <- App (App (Var (varNameM -> "&&")) a) b

pattern OrInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern OrInfix a b <- App (App (Var (varNameM -> "||")) a) b where
  OrInfix a b = App (App (Var (mkVar @(E ctx) "||")) a) b

pattern OrInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern OrInfix' a b <- App (App (Var (varNameM -> "||")) a) b

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

pattern SubtractSat' :: forall ctx. E ctx -> E ctx -> E ctx
pattern SubtractSat' a b <- App (App (Var (varNameM -> "-subtractSat")) a) b

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

pattern Negate' :: forall ctx. E ctx -> E ctx
pattern Negate' a <- App (Var (varNameM -> "negate")) a

pattern MinusU :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern MinusU a <- App (Var (varNameM -> "minusU")) a where
  MinusU a = App (Var (mkVar @(E ctx) "minusU")) a

pattern MinusU' :: forall ctx. E ctx -> E ctx
pattern MinusU' a <- App (Var (varNameM -> "minusU")) a

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

pattern Dim :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Dim a <- App (Var (varNameM -> "dim")) a where
  Dim a = App (Var (mkVar @(E ctx) "dim")) a

pattern MatrixSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx -> E ctx
pattern MatrixSat r c f <- App (App (App (Var (varNameM -> "matrix")) r) c) f where
  MatrixSat r c f = App (App (App (Var (mkVar @(E ctx) "matrix")) r) c) f

pattern VectorSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern VectorSat r f <- App (App (Var (varNameM -> "vector")) r) f where
  VectorSat r f = App (App (Var (mkVar @(E ctx) "vector")) r) f

pattern ConsSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern ConsSat h t <- App (App (Var (varNameM -> "cons")) h) t where
  ConsSat h t = App (App (Var (mkVar @(E ctx) "cons")) h) t

pattern Length :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Length a <- App (Var (varNameM -> "length")) a where
  Length a = App (Var (mkVar @(E ctx) "length")) a
