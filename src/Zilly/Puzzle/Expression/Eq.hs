{-# OPTIONS_GHC -Wno-orphans          #-}

module Zilly.Puzzle.Expression.Eq
  ( Eq
  ) where

import Zilly.Puzzle.Expression.Base
import Zilly.Puzzle.Environment.TypedMap

instance Eq (E ctx) where
  ValZ a == ValZ b = a == b
  ValF a == ValF b = a == b
  ValB a == ValB b = a == b
  ValS a == ValS b = a == b
  ValZ a == ValF b = fromIntegral a == b
  ValF a == ValZ b = a == fromIntegral b
  Var x == Var y = varNameM x == varNameM y
  MkArray xs == MkArray ys = xs == ys
  Defer a == Defer b = a == b
  Defer a == LazyC _ b _ = a == b
  LazyC _ a _ == Defer b = a == b
  LazyC _ a _ == LazyC _ b _ = a == b
  Lambda (t,_) x body == Lambda (t',_) x' body'
    = t == t' && varNameM x == varNameM x' && body == body'
  LambdaC (t,_) _ x body == LambdaC (t',_) _ x' body'
    = t == t' && varNameM x == varNameM x' && body == body'
  If c t f == If c' t' f'
    = c == c' && t == t' && f == f'
  ArraySlice a b == ArraySlice a' b'
    = a == a' && b == b'
  App f x == App f' x'
    = f == f' && x == x'
  _ == _ = False
