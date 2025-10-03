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
  , ltStd'
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
  $ MinusInfix (Formula $$ VarS "y") (Formula $$ VarS "x")


minusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
minusStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ MinusInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

plusStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
plusStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ PlusInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

timesStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
timesStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ TimesInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

divStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
divStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ DivInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

powStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
powStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ PowInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

appendStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
appendStd
  = Lambda (ZString, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (ZString, Nothing) (mkVar @(E ctx) "y")
  $ AppendInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

andStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
andStd
  = Lambda (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (ZBool, Nothing) (mkVar @(E ctx) "y")
  $ AndInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

orStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
orStd
  = Lambda (ZBool, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (ZBool, Nothing) (mkVar @(E ctx) "y")
  $ OrInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

ltStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
ltStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ LTInfix (Formula $$ VarS "y") (Formula $$ VarS "x")

ltStd' :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
ltStd'
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ If (LTInfix (Formula $$ VarS "y") (Formula $$ VarS "x"))
        (ValZ 1)
        (ValZ 0)

leStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
leStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ LEInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

gtStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
gtStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ GTInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

geStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
geStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ GEInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

eqStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
eqStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ EQInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

neStd :: forall {m} ctx. (CtxConstraint ctx m) =>  E ctx
neStd
  = Lambda (Z, Nothing) (mkVar @(E ctx) "x")
  $ Lambda (Z, Nothing) (mkVar @(E ctx) "y")
  $ NEInfix (Formula $$ VarS "x") (Formula $$ VarS "y")

eStd :: E ctx
eStd = ValF 2.718281828459045
