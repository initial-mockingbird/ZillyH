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
  Var _ x == Var _ y = varNameM x == varNameM y
  MkArray  _ xs == MkArray _ ys = xs == ys
  Defer _ a == Defer _ b = a == b
  Defer _ a == LazyC _ _ b _ = a == b
  LazyC _ _ a _ == Defer _ b = a == b
  LazyC _ _ a _ == LazyC _ _ b _ = a == b
  Lambda _ (t,_) x body == Lambda _ (t',_) x' body'
    = t == t' && varNameM x == varNameM x' && body == body'
  LambdaC _ (t,_) _ x body == LambdaC _ (t',_) _ x' body'
    = t == t' && varNameM x == varNameM x' && body == body'
  If _ c t f == If _ c' t' f'
    = c == c' && t == t' && f == f'
  ArraySlice _ a b == ArraySlice _ a' b'
    = a == a' && b == b'
  App _ f x == App _ f' x'
    = f == f' && x == x'
  MkTuple _ a b xs == MkTuple _ a' b' xs'
    = a == a' && b == b' && xs == xs'
  DotApp _ a s == DotApp _ a' s'
    = a == a' && s == s'
  Cons _ s xs == Cons _ s' xs'
    = s == s' && xs == xs'
  ConsV _ s xs == ConsV _ s' xs'
    = s == s' && xs == xs'
  ARecord _ xs == ARecord _ ys
    = length xs == length ys && all (\((n1,e1),(n2,e2)) -> n1 == n2 && e1 == e2) (zip xs ys)
  ARecordV _ xs == ARecordV _ ys
    = length xs == length ys && all (\((n1,e1),(n2,e2)) -> n1 == n2 && e1 == e2) (zip xs ys)
  Match _ a ps == Match _ a' ps'
    = a == a' && length ps == length ps' && all (\((p1,e1),(p2,e2)) -> p1 == p2 && e1 == e2) (zip ps ps')
  _ == _ = False
