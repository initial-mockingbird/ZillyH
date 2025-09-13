{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE FlexibleContexts    #-}

module Zilly.Puzzle.Expression.Std
  ( uminusStd
  , negateStd
  , subStd
  , minusStd
  , plusStd
  , timesStd
  , divStd
  , powStd
  , appendStd
  , andStd
  , orStd
  , ltStd
  , leStd
  , gtStd
  , geStd
  , eqStd
  , neStd
  , eStd
  ) where

import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Expression.Patterns
import Zilly.Puzzle.Expression.Interpreter
import Zilly.Puzzle.Environment.TypedMap
import Zilly.Puzzle.Types.Exports

uminusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
uminusStd
  = Lambda (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ MinusU (Formula $$ VarS Z "x")

negateStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
negateStd
  = Lambda (ZBool :-> ZBool) (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Negate (Formula $$ VarS ZBool "x")

subStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
subStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ MinusInfix (Formula $$ VarS Z "y") (Formula $$ VarS Z "x")


minusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
minusStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ MinusInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

plusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
plusStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ PlusInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

timesStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
timesStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ TimesInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

divStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
divStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ DivInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

powStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
powStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ PowInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

appendStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
appendStd
  = Lambda (ZString :-> ZString :-> ZString) (ZString, Nothing) (mkVar @(E ctx) "x")
  $ Lambda             (ZString :-> ZString) (ZString, Nothing) (mkVar @(E ctx) "y")
  $ AppendInfix (Formula $$ VarS ZString "x") (Formula $$ VarS ZString "y")

andStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
andStd
  = Lambda (ZBool :-> ZBool :-> ZBool) (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Lambda           (ZBool :-> ZBool) (ZBool, Nothing) (mkVar @(E ctx) "y")
  $ AndInfix (Formula $$ VarS ZBool "x") (Formula $$ VarS ZBool "y")

orStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
orStd
  = Lambda (ZBool :-> ZBool :-> ZBool) (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Lambda           (ZBool :-> ZBool) (ZBool, Nothing) (mkVar @(E ctx) "y")
  $ OrInfix (Formula $$ VarS ZBool "x") (Formula $$ VarS ZBool "y")

ltStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
ltStd
  = Lambda (Z :-> Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> Z) (Z, Nothing) (mkVar @(E ctx) "y")
  $ If Z (LTInfix (Formula $$ VarS Z "y") (Formula $$ VarS Z "x")) (ValZ 1) (ValZ 0)

leStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
leStd
  = Lambda (Z :-> Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "y")
  $ LEInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

gtStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
gtStd
  = Lambda (Z :-> Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "y")
  $ GTInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

geStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
geStd
  = Lambda (Z :-> Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "y")
  $ GEInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

eqStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
eqStd
  = Lambda (Z :-> Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "y")
  $ EQInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

neStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
neStd
  = Lambda (Z :-> Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda       (Z :-> ZBool) (Z, Nothing) (mkVar @(E ctx) "y")
  $ NEInfix (Formula $$ VarS Z "x") (Formula $$ VarS Z "y")

eStd :: E ctx
eStd = ValF 2.718281828459045
