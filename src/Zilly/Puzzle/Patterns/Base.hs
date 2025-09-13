{-# LANGUAGE GADTs        #-}
{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Zilly.Puzzle.Patterns.Base
  ( LPattern(..)
  , PatternGuard(..)
  , Pattern(..)
  , PatternCtx
  , lPatternVars
  , patternGuardVars
  ) where

import Data.Kind (Type)
import Zilly.Puzzle.Types.Exports

data LPattern ctx where
  LVar    :: String -> LPattern ctx
  LWild   :: LPattern ctx
  LInt    :: Int -> LPattern ctx
  LBool   :: Bool -> LPattern ctx
  LString :: String -> LPattern ctx
  LFloat  :: Double -> LPattern ctx
  LTuple  :: LPattern ctx -> LPattern ctx -> [LPattern ctx] -> LPattern ctx
  LCons   :: String -> [LPattern ctx] -> LPattern ctx
  LARecord :: [(String, Types)] -> LPattern ctx

lPatternVars :: LPattern ctx -> [String]
lPatternVars (LVar  n)          = [n]
lPatternVars (LTuple  p1 p2 ps) = lPatternVars p1 ++ lPatternVars p2 ++ concatMap lPatternVars ps
lPatternVars (LCons  _ ps)      = concatMap lPatternVars ps
lPatternVars (LARecord  xs)     = fst <$> xs
lPatternVars _                  = []

data PatternGuard expr ctx where
  ExprGuard :: expr -> PatternGuard expr ctx
  BindingGuard :: LPattern ctx -> expr -> PatternGuard expr ctx

patternGuardVars :: PatternGuard expr ctx -> [String]
patternGuardVars (ExprGuard  _ )          = []
patternGuardVars (BindingGuard  p _ )     = lPatternVars p


data Pattern expr ctx where
  Pattern :: LPattern ctx -> [PatternGuard expr ctx] -> Pattern expr ctx

type family PatternCtx (expr :: Type) (ctx :: Type) :: Type

instance Eq (LPattern ctx) where
  (LVar  n1)       == (LVar  n2)       = n1 == n2
  (LWild )         == (LWild )         = True
  (LInt  i1)       == (LInt  i2)       = i1 == i2
  (LBool  b1)      == (LBool b2)      = b1 == b2
  (LString  s1)    == (LString  s2)    = s1 == s2
  (LFloat  f1)     == (LFloat  f2)     = f1 == f2
  (LTuple  p1a p1b ps1) == (LTuple  p2a p2b ps2) = p1a == p2a && p1b == p2b && ps1 == ps2
  (LCons  n1 ps1)  == (LCons  n2 ps2)  = n1 == n2 && ps1 == ps2
  (LARecord  fs1)  == (LARecord  fs2)  = fs1 == fs2
  _                 == _                 = False

instance Eq expr => Eq (PatternGuard expr ctx) where
  (ExprGuard  e1)          == (ExprGuard  e2)          = e1 == e2
  (BindingGuard  p1 e1)    == (BindingGuard  p2 e2)    = p1 == p2 && e1 == e2
  _                         == _                         = False

instance Eq expr => Eq (Pattern expr ctx) where
  (Pattern  lp1 gs1) == (Pattern  lp2 gs2) = lp1 == lp2 && gs1 == gs2
