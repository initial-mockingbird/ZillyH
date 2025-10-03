{-# Language PatternSynonyms          #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE BangPatterns             #-}

module Zilly.Puzzle.Types.Patterns
  ( pattern Z
  , pattern F
  , pattern Top
  , pattern Bot
  , pattern ZString
  , pattern ZBool
  , pattern ZNull
  , pattern ZDouble
  , pattern ZInfer
  , pattern ZArray
  , pattern NDArray
  , pattern Lazy
  , pattern Tuple
  , pattern NTuple
  , pattern (:->)
  , pattern ARecord
  , pattern RV
  , pattern NatDataKind
  , pattern IsBoolean
  , pattern TConstraints
  , pattern StringDataKind
  ) where

import Zilly.Puzzle.Types.Types
import Data.Text qualified as Text
import Text.Read (readMaybe)
import Data.Set (Set)
import Data.Set qualified as S

infixr 0 :->

pattern Z       :: Types
pattern F       :: Types
pattern Top     :: Types
pattern Bot     :: Types
pattern ZString :: Types
pattern ZBool   :: Types
pattern ZNull   :: Types
pattern ZDouble :: Types
pattern ZInfer  :: Types
pattern ZArray  :: Types -> Types
pattern Lazy    :: Types -> Types
pattern Tuple   :: Types -> Types -> Types
pattern NTuple  :: Types -> Types -> [Types] -> Types
pattern (:->)   :: Types -> Types -> Types

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
pattern ZArray a  = TCon "array" [a]

pattern NDArray :: Int -> Types -> Types
pattern NDArray n a <- (TCon "array" [NatDataKind n,a])
  where NDArray n a = TCon "array"  [NatDataKind n, a]


pattern ARecord :: [(Text.Text, Types)] -> Types
pattern ARecord fields <- TCon "~Record" (fmap (\(TCon k [v]) -> (k,v)) -> fields)
  where ARecord fields = TCon "~Record" [TCon k [v] | (k,v) <- fields]


pattern RV :: Types -> Types
pattern RV t <- TFamApp "RV" t []
  where RV t = TFamApp "RV" t []


pattern NatDataKind :: Int -> Types
pattern NatDataKind n <- TCon (readMaybe . Text.unpack -> Just n) []
  where NatDataKind n = TCon (Text.pack (show n)) []


pattern StringDataKind :: Text.Text -> Types
pattern StringDataKind s <- TCon s []
  where StringDataKind s = TCon s []

pattern IsBoolean :: Types -> Types
pattern IsBoolean t <- TConstraint "IsBoolean" t [] ((== t) -> True)
  where IsBoolean t = TConstraint "IsBoolean" t [] t

pattern TConstraints :: Set (Name, Types, [Types]) -> Types -> Types
pattern TConstraints cs t <- (goTConstraints -> (cs, t))
  where TConstraints cs t = S.foldr (\(c, t1, ts) acc -> TConstraint c t1 ts acc) t cs



goTConstraints :: Types -> (Set (Name, Types, [Types]), Types)
goTConstraints (TConstraint c t ts t2) =
  let (s,t3) = goTConstraints t2
  in (S.insert (c, t, ts) s, t3)
goTConstraints t = (S.empty, t)
