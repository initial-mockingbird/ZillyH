{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE OverloadedStrings     #-}

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
  , pattern FormulaApp
  , pattern RandomApp
  , pattern HeadApp
  , pattern TailApp
  , pattern ConsRecordSingleV
  , pattern ConsRecordSingleV'
  , ($$)
  ) where

import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Environment.TypedMap
import Control.Monad.IO.Class
import Control.Monad.Error.Class
import Zilly.Puzzle.Types.Exports hiding (ARecord)
import Zilly.Puzzle.Expression.Classes (typeOf)


-------------------------------
-- Aux functions and patterns
-------------------------------

infixl 1 $$

($$) :: E ctx -> E ctx -> E ctx
($$) a b = case typeOf a of
  (_ :-> ret) -> App ret a b
  _           -> error $ "Cannot apply non-function type: " ++ show (typeOf a)

mkBinOp :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => String -> E ctx -> E ctx -> E ctx
mkBinOp op a b =
  let ta = typeOf a
      tb = typeOf b
      u  = unsafeUpperBound ta tb
  in App u (App (u :-> u) (Var (u :-> u :-> u)  (mkVar @(E ctx) op)) a) b

pattern BinOpDestructor :: forall ctx.
  String -> E ctx -> E ctx -> E ctx
pattern BinOpDestructor op a b <- App _ (App _ (Var _ (varNameM -> op)) a) b

------------------------
-- Expression patterns
------------------------

pattern VarS :: forall {m} ctx. (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m) => Types -> String -> E ctx
pattern VarS t s <- Var t (varNameM -> s) where
  VarS t s = Var t (mkVar @(E ctx) s)

pattern Formula :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
pattern Formula <- Var _ (varNameM -> "formula") where
  Formula  = Var ("a" :-> "a")  (mkVar @(E ctx) "formula")

pattern FormulaApp :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx
pattern FormulaApp a <- App _ (Var _ (varNameM -> "formula")) a where
  FormulaApp a =
    let ta = typeOf a
    in App ta (Var (ta :-> ta) (mkVar @(E ctx) "formula")) a

pattern Random :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => Types -> E ctx
pattern Random t <- Var t (varNameM -> "random") where
  Random t = Var t (mkVar @(E ctx) "random")

pattern RandomApp :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx
pattern RandomApp a <- App _ (Var _ (varNameM -> "random")) a where
  RandomApp a =
    let ta = typeOf a
    in App ta (Var (ta :-> ta) (mkVar @(E ctx) "random")) a

pattern Head :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
pattern Head <- Var _ (varNameM -> "head") where
  Head = Var (ZString :-> ZString) (mkVar @(E ctx) "head")

pattern HeadApp :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx
pattern HeadApp a <- App _ (Var _ (varNameM -> "head")) a where
  HeadApp a = App ZString (Var (ZString :-> ZString) (mkVar @(E ctx) "head")) a

pattern Tail :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
pattern Tail <- Var _ (varNameM -> "tail") where
  Tail = Var (ZString :-> ZString) (mkVar @(E ctx) "tail")

pattern TailApp :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx
pattern TailApp a <- App _ (Var _ (varNameM -> "tail")) a where
  TailApp a = App ZString (Var (ZString :-> ZString) (mkVar @(E ctx) "tail")) a

pattern MinusInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern MinusInfix a b <- BinOpDestructor "-" a b where
  MinusInfix a b = mkBinOp "-" a b

pattern MinusInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern MinusInfix' a b <- BinOpDestructor "-" a b


pattern PlusInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern PlusInfix a b <- BinOpDestructor "+" a b where
  PlusInfix a b = mkBinOp "+" a b

pattern PlusInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern PlusInfix' a b <- BinOpDestructor "+" a b

pattern TimesInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern TimesInfix a b <- BinOpDestructor "*" a b where
  TimesInfix a b = mkBinOp "*" a b

pattern TimesInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern TimesInfix' a b <- BinOpDestructor "*" a b


pattern DivInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx
  -> E ctx
  -> E ctx
pattern DivInfix a b <- BinOpDestructor "/" a b where
  DivInfix a b = mkBinOp "/" a b

pattern DivInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern DivInfix' a b <- BinOpDestructor "/" a b

pattern PowInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m )
  => E ctx -> E ctx -> E ctx
pattern PowInfix a b <- BinOpDestructor "^" a b where
  PowInfix a b = mkBinOp "^" a b

pattern PowInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern PowInfix' a b <- BinOpDestructor "^" a b

pattern LTInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LTInfix a b <- BinOpDestructor "<" a b where
  LTInfix a b = mkBinOp "<" a b

pattern LTInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern LTInfix' a b <- BinOpDestructor "<" a b

pattern LEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern LEInfix a b <- BinOpDestructor "<=" a b where
  LEInfix a b = mkBinOp "<=" a b

pattern LEInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern LEInfix' a b <- BinOpDestructor "<=" a b

pattern GTInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GTInfix a b <- BinOpDestructor ">" a b where
  GTInfix a b = mkBinOp ">" a b

pattern GTInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern GTInfix' a b <- BinOpDestructor ">" a b

pattern GEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern GEInfix a b <- BinOpDestructor ">=" a b where
  GEInfix a b = mkBinOp ">=" a b

pattern GEInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern GEInfix' a b <- BinOpDestructor ">=" a b

pattern EQInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern EQInfix a b <- BinOpDestructor "=" a b where
  EQInfix a b = mkBinOp "=" a b

pattern EQInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern EQInfix' a b <- BinOpDestructor "=" a b

pattern NEInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern NEInfix a b <- BinOpDestructor "<>" a b where
  NEInfix a b = mkBinOp "<>" a b

pattern NEInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern NEInfix' a b <- BinOpDestructor "<>" a b

pattern AppendInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern AppendInfix a b <- BinOpDestructor "++" a b where
  AppendInfix a b = mkBinOp "++" a b

pattern AppendInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern AppendInfix' a b <- BinOpDestructor "++" a b

pattern AndInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern AndInfix a b <- BinOpDestructor "&&" a b where
  AndInfix a b = mkBinOp "&&" a b

pattern AndInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern AndInfix' a b <- BinOpDestructor "&&" a b

pattern OrInfix :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern OrInfix a b <- BinOpDestructor "||" a b where
  OrInfix a b = mkBinOp "||" a b

pattern OrInfix' :: forall ctx. E ctx -> E ctx -> E ctx
pattern OrInfix' a b <- BinOpDestructor "||" a b


pattern SubtractSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m)
  => E ctx -> E ctx -> E ctx
pattern SubtractSat a b <- BinOpDestructor "-subtractSat" a b where
  SubtractSat a b = mkBinOp "-subtractSat" a b

pattern SubtractSat' :: forall ctx. E ctx -> E ctx -> E ctx
pattern SubtractSat' a b <- BinOpDestructor "-subtractSat" a b


pattern MinusUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern MinusUnsat t <- Var t (varNameM -> "minus") where
  MinusUnsat t = Var t (mkVar @(E ctx) "minus")


pattern PlusUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern PlusUnsat t <- Var t (varNameM -> "plus") where
  PlusUnsat t = Var t (mkVar @(E ctx) "plus")

pattern TimesUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern TimesUnsat t <- Var t (varNameM -> "times") where
  TimesUnsat t = Var t (mkVar @(E ctx) "times")

pattern DivUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern DivUnsat t <- Var t (varNameM -> "div") where
  DivUnsat t = Var t (mkVar @(E ctx) "div")

pattern PowUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern PowUnsat t <- Var t (varNameM -> "pow") where
  PowUnsat t = Var t (mkVar @(E ctx) "pow")

pattern AppendUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern AppendUnsat <- Var _ (varNameM -> "append") where
  AppendUnsat = Var (ZString :-> ZString) (mkVar @(E ctx) "append")

pattern AndUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern AndUnsat <- Var _ (varNameM -> "and") where
  AndUnsat = Var (ZBool :-> ZBool) (mkVar @(E ctx) "and")

pattern OrUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx
pattern OrUnsat <- Var _ (varNameM -> "or") where
  OrUnsat = Var (ZBool :-> ZBool) (mkVar @(E ctx) "or")

pattern SubtractUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern SubtractUnsat t <- Var t (varNameM -> "subtract") where
  SubtractUnsat t = Var t (mkVar @(E ctx) "subtract")

pattern LTSatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern LTSatUnsat t <- Var t (varNameM -> "lt") where
  LTSatUnsat t = Var t (mkVar @(E ctx) "lt")

pattern LESatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern LESatUnsat t <- Var t (varNameM -> "le") where
  LESatUnsat t = Var t (mkVar @(E ctx) "le")

pattern GTSatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern GTSatUnsat t <- Var t (varNameM -> "gt") where
  GTSatUnsat t = Var t (mkVar @(E ctx) "gt")

pattern GESatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern GESatUnsat t <- Var t (varNameM -> "ge") where
  GESatUnsat t = Var t (mkVar @(E ctx) "ge")

pattern EQSatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern EQSatUnsat t <- Var t (varNameM -> "eq") where
  EQSatUnsat t = Var t (mkVar @(E ctx) "eq")

pattern NESatUnsat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => Types -> E ctx
pattern NESatUnsat t <- Var t (varNameM -> "ne") where
  NESatUnsat t = Var t (mkVar @(E ctx) "ne")

pattern A_1 :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern A_1 a <- App _ (Var _ (varNameM -> "_1")) a where
  A_1 a = case typeOf a of
    ta@(NTuple _1 _ _)
      -> App _1 (Var (ta :-> _1) (mkVar @(E ctx) "_1")) a
    _ -> error $ "A_1 pattern: expected tuple type, got " ++ show (typeOf a)

pattern A_2 :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern A_2 a <- App _ (Var _ (varNameM -> "_2")) a where
  A_2 a = case typeOf a of
    ta@(NTuple _ _2 _)
      -> App _2 (Var (ta :-> _2) (mkVar @(E ctx) "_2")) a
    _ -> error $ "A_2 pattern: expected tuple type, got " ++ show (typeOf a)

pattern Negate :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Negate a <- App _ (Var _ (varNameM -> "negate")) a where
  Negate a = App ZBool (Var (ZBool :-> ZBool) (mkVar @(E ctx) "negate")) a

pattern Negate' :: forall ctx. E ctx -> E ctx
pattern Negate' a <- App _ (Var _ (varNameM -> "negate")) a

pattern MinusU :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern MinusU a <- App _ (Var _ (varNameM -> "minusU")) a where
  MinusU a =
    let ta = typeOf a
    in App ta (Var (ta :-> ta) (mkVar @(E ctx) "minusU")) a

pattern MinusU' :: forall ctx. E ctx -> E ctx
pattern MinusU' a <- App _ (Var _ (varNameM -> "minusU")) a

pattern LogE :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern LogE a <- App _ (Var _ (varNameM -> "log")) a where
  LogE a = App F (Var (F :-> F) (mkVar @(E ctx) "log")) a


pattern Sin :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Sin a <- App _ (Var _ (varNameM -> "sin")) a where
  Sin a = App F (Var (F :-> F) (mkVar @(E ctx) "sin")) a

pattern Cos :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Cos a <- App _ (Var _ (varNameM -> "cos")) a where
  Cos a = App F (Var (F :-> F) (mkVar @(E ctx) "cos")) a

pattern Tan :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Tan a <- App _ (Var _ (varNameM -> "tan")) a where
  Tan a = App F (Var (F :-> F) (mkVar @(E ctx) "tan")) a


pattern ASin :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern ASin a <- App _ (Var _ (varNameM -> "asin")) a where
  ASin a = App F (Var (F :-> F) (mkVar @(E ctx) "asin")) a

pattern ACos :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern ACos a <- App _ (Var _ (varNameM -> "acos")) a where
  ACos a = App F (Var (F :-> F) (mkVar @(E ctx) "acos")) a

pattern ATan :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern ATan a <- App _ (Var _ (varNameM -> "atan")) a where
  ATan a = App F (Var (F :-> F) (mkVar @(E ctx) "atan")) a

pattern Dim :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Dim a <- App _ (Var _ (varNameM -> "dim")) a where
  Dim a = case typeOf a of
    ta@(NDArray n t) -> App (NDArray n Z) (Var (ta :-> NDArray n Z) (mkVar @(E ctx) "dim")) a
    _ -> error $ "Dim pattern: expected array type, got " ++ show (typeOf a)

pattern MatrixSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx -> E ctx
pattern MatrixSat r c f <- App _ (App _ (App _ (Var _ (varNameM -> "matrix")) r) c) f where
  MatrixSat r c f = case typeOf f of
    tf@(_ :-> _ :-> ret)
      -> App ret (App (tf :-> ret)  (App (Z :-> tf :-> ret) (Var (Z :-> Z :-> tf :-> ret) (mkVar @(E ctx) "matrix")) r) c) f
    _ -> error $ "MatrixSat pattern: expected function type, got " ++ show (typeOf f)

pattern VectorSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern VectorSat r f <- App _ (App _ (Var _ (varNameM -> "vector")) r) f where
  VectorSat r f = case typeOf f of
    tf@(_ :-> ret)
      -> App ret (App (tf :-> ret) (Var (Z :-> tf :-> ret) (mkVar @(E ctx) "vector")) r) f
    _ -> error $ "VectorSat pattern: expected function type, got " ++ show (typeOf f)

pattern ConsSat :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx -> E ctx
pattern ConsSat h t <- App _ (App _ (Var _ (varNameM -> "cons")) h) t where
  ConsSat h t = case typeOf t of
    tt@(NDArray n base) -> App tt (App (tt :-> tt) (Var (base :-> tt :-> tt) (mkVar @(E ctx) "cons")) h) t
    _ -> error $ "ConsSat pattern: expected array type, got " ++ show (typeOf t)

pattern Length :: forall {m} ctx.
  (EvalMonad (E ctx) ~ m, MonadIO m, MonadError String m
  ) => E ctx -> E ctx
pattern Length a <- App _ (Var _ (varNameM -> "length")) a where
  Length a =
    let ta = typeOf a
    in App Z (Var (ta :-> Z) (mkVar @(E ctx) "length")) a

pattern ConsRecordSingleV' :: String -> [(String, E ctx)] -> E ctx
pattern ConsRecordSingleV' consName fields <- ConsV _ consName [ARecordV _ fields]

pattern ConsRecordSingleV :: Types -> Types -> String -> [(String, E ctx)] -> E ctx
pattern ConsRecordSingleV consT recT consName fields <- ConsV consT consName [ARecordV recT fields] where
  ConsRecordSingleV consT recT consName fields = Cons consT consName [ARecord recT fields]
