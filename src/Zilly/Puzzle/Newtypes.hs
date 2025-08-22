{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE TypeAbstractions         #-}
{-# Language PatternSynonyms          #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TupleSections #-}

module Zilly.Puzzle.Newtypes where

import Data.String
import Data.Text (Text)
import Data.Text qualified as Text
import Unsafe.Coerce
import Text.Read (readMaybe)

type Name  = Text


newtype TVar  = TV Name deriving (Eq,Ord)

data Types
  = TCon Name [Types]
  | TVar TVar
  deriving (Eq,Ord)


infixr 0 :->
pattern Z         = TCon "Z"      []
pattern a :-> b   = TCon "->"     [a, b]
pattern Lazy a    = TCon "Lazy"   [a]
pattern Tuple a b = TCon "Tuple"  [a,b]
pattern NTuple a b xs = TCon "Tuple" (a:b:xs)
pattern Top       = TCon "Top"    []
pattern Bot       = TCon "Bot"    []
pattern F         = TCon "R"      []
pattern ZString   = TCon "String" []
pattern ZBool     = TCon "B"   []
pattern ZNull     = TCon "Null"   []
pattern ZDouble   = TCon "R"      []
pattern ZInfer    = TCon "Infer"  []
pattern ZArray a  = TCon "Array" [a]

pattern NDArray :: Int -> Types -> Types
pattern NDArray n a <- (_ndaux -> Just (n,a))
  where NDArray n a = TCon ("array" <> Text.pack (show n)) [a]

_ndaux :: Types -> Maybe (Int, Types)
_ndaux t@(TCon _ [a]) = (,a) <$> getArrDimType t
_ndaux _ = Nothing


getArrDimType :: Types -> Maybe Int
getArrDimType (TCon name [a])
  | Text.isPrefixOf "array" name = readMaybe $ Text.unpack $ Text.drop 5 name
getArrDimType _ = Nothing


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

instance Show Types where
  showsPrec p = \case
    TCon a [] -> showString $ Text.unpack a
    NDArray n a
      -> showString "array["
      . showString (replicate (n-1) ',')
      . showString "]<"
      . shows a
      . showString ">"
    TCon "Tuple" [a,b] -> showString "(" . shows a . showString ", " . shows b . showString ")"
    a :-> b -> showParen (p > 0) $ showsPrec 1 a . showString " => " . showsPrec 0 b
    TCon a (x:xs)
      -> showString (Text.unpack a) . showString "<"
      . (foldr (\arg acc -> shows arg . showString ", " . acc) (shows x) xs)
      . showString ">"
    TVar (TV n) -> showString $ Text.unpack n
