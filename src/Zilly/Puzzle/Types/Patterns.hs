{-# Language PatternSynonyms          #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE ImportQualifiedPost      #-}


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
  , getArrDimType
  ) where

import Zilly.Puzzle.Types.Types
import Data.Text qualified as Text
import Text.Read (readMaybe)


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
pattern ZArray a  = TCon "Array" [a]

pattern NDArray :: Int -> Types -> Types
pattern NDArray n a <- (_ndaux -> Just (n,a))
  where NDArray n a = TCon ("array" <> Text.pack (show n)) [a]

_ndaux :: Types -> Maybe (Int, Types)
_ndaux t@(TCon _ [a]) = (,a) <$> getArrDimType t
_ndaux _ = Nothing

getArrDimType :: Types -> Maybe Int
getArrDimType (TCon name [_])
  | Text.isPrefixOf "array" name = readMaybe $ Text.unpack $ Text.drop 5 name
getArrDimType _ = Nothing
