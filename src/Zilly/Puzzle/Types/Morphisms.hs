module Zilly.Puzzle.Types.Morphisms
  ( rtype
  , isSuperTypeOf
  , isSubtypeOf
  ) where

import Zilly.Puzzle.Types.Types
import Zilly.Puzzle.Types.Patterns

rtype :: Types -> Types
rtype (Lazy a) = a
rtype (a :-> b) = a :-> b
rtype (NDArray n a) = NDArray n (rtype a)
rtype (TCon n xs) = TCon n (rtype <$> xs)
rtype (TVar _) = error "cannot rtype a type variable at the moment."


isSuperTypeOf :: Types -> Types -> Bool
isSuperTypeOf F Z = True
isSuperTypeOf (NDArray n a) (NDArray m b) = n == m && isSuperTypeOf a b
isSuperTypeOf (Lazy a) (Lazy b) = isSuperTypeOf a b
isSuperTypeOf (Lazy a) b = isSuperTypeOf a b
isSuperTypeOf (NTuple a b xs) (NTuple c d ys) = length xs <= length ys
  && isSuperTypeOf a c && isSuperTypeOf b d
  && all (uncurry isSuperTypeOf) (zip xs ys)
isSuperTypeOf (a :-> b) (c :-> d) = isSubtypeOf a c && isSuperTypeOf b d
isSuperTypeOf (TVar _) _ = True
isSuperTypeOf _ (TVar _) = True
isSuperTypeOf a b = a == b

isSubtypeOf :: Types -> Types -> Bool
isSubtypeOf Z F = True
isSubtypeOf (NDArray n a) (NDArray m b) = n == m && isSubtypeOf a b
isSubtypeOf (Lazy a) (Lazy b) = isSubtypeOf a b
isSubtypeOf (NTuple a b xs) (NTuple c d ys) = length xs >= length ys
  && isSubtypeOf a c && isSubtypeOf b d
  && all (uncurry isSubtypeOf) (zip xs ys)
isSubtypeOf (a :-> b) (c :-> d) = isSuperTypeOf a c && isSubtypeOf b d
isSubtypeOf (TVar _) _ = True
isSubtypeOf _ (TVar _) = True
isSubtypeOf a b = a == b
