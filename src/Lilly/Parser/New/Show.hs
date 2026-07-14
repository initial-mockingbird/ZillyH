{-|
Module      : Lilly.Parser.New.Show
Description : Provides a way @toString@ decorated IR ASTs.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.New.Show where

import Lilly.Parser.IR.Exports
import Lilly.Parser.New.Utilities
import Data.Fix
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Data.List (unsnoc)

newtype ShowCtx = ShowCtx 
  { precedenceTable :: PrecedenceTable 

  }
data LillyExprP = LillyExprP 
  { unLillyExprP :: Expression
  , lillyExprPShowCtx :: ShowCtx
  }
data LillyPatternP = LillyPatternP 
  { unLillyPatternP :: Pattern
  , lillyPatternPShowCtx :: ShowCtx
  }
data LillyGuardP = LillyGuardP 
  { unLillyGuardP :: Guard
  , lillyGuardPShowCtx :: ShowCtx
  }
data LillyTypeP = LillyTypeP 
  { unLillyTypeP :: Types
  , lillyTypePShowCtx :: ShowCtx
  }

class HasShowCtx a where
  getShowCtx :: a -> ShowCtx

instance HasShowCtx LillyExprP where
  getShowCtx = lillyExprPShowCtx
instance HasShowCtx LillyPatternP where
  getShowCtx = lillyPatternPShowCtx
instance HasShowCtx LillyGuardP where
  getShowCtx = lillyGuardPShowCtx
instance HasShowCtx LillyTypeP where
  getShowCtx = lillyTypePShowCtx


type Precedence = Int
type PrecedenceTable = Map Text (Fixity, Precedence)


showsInfixR :: (Show a) => Int -> Int -> Operator -> a -> a -> ShowS
showsInfixR p n op l r = showParen (p > n) 
  $ showsPrec (n+1) l
  . showString " "
  . showString (Text.unpack op)
  . showString " " 
  . showsPrec n r

showsInfixL :: (Show a) => Int -> Int -> Operator -> a -> a -> ShowS
showsInfixL p n op l r = showParen (p > n) 
  $ showsPrec n l 
  . showString " "
  . showString (Text.unpack op)
  . showString " " 
  . showsPrec (n+1) r

showsInfix :: (Show a) => Int -> Int -> Operator -> a -> a -> ShowS
showsInfix p n op l r = showParen (p > n)
  $ showsPrec (n+1) l
  . showString " "
  . showString (Text.unpack op)
  . showString " " 
  . showsPrec (n+1) r


-- We use Show till TextShow is available (we gotta bump the version of ghc)
instance Show  LillyTypeP where
  showsPrec p (LillyTypeP (Fix t) shwCtx) = case t of 
    PTZ -> showString "Z"
    PTR -> showString "R"
    PTB -> showString "B"
    PTString -> showString "String"
    PTLazy a 
      -> showString "lazy<" . shows (LillyTypeP a shwCtx) . showString ">"
    PTArray d a 
      -> showString "array[" . showString (replicate (d-1) ',') . showString "]" 
      . showString "<" . shows (LillyTypeP a shwCtx) . showString ">"
    PTNtuple (a1,a2) as
      -> showString "(" 
      . foldr (\x acc -> shows (LillyTypeP x shwCtx) . showString ", " . acc)
              (shows . flip LillyTypeP shwCtx $ l)  hs
      . showString ")"
      where Just (hs,l) = unsnoc (a1 : a2 : as)
    PTPolymorphic name as -> case as of 
      [] -> showString (Text.unpack name)
      _  -> let Just (hs,l) = unsnoc as 
        in showString (Text.unpack name)
        <> showString "<" 
        <> foldr (\x acc -> shows (LillyTypeP x shwCtx) . showString ", " . acc)
              (shows . flip LillyTypeP shwCtx $ l) hs 
        <> showString ">" 
    PTUserDefined name as -> case as of 
      [] -> showString (Text.unpack name)
      _  -> let Just (hs,l) = unsnoc as
        in showString (Text.unpack name)  
        <> showString "<"
        <> foldr (\x acc -> shows (LillyTypeP x shwCtx) . showString ", " . acc)
                (shows . flip LillyTypeP shwCtx $ l) hs
    PArrow a1 a2-> showsInfixR p 3 "=>" (LillyTypeP a1 shwCtx) (LillyTypeP a2 shwCtx)

instance Show  LillyExprP where
  showsPrec p (LillyExprP (Expression e) shwCtx) = case e of 
    PVariable name -> showString (Text.unpack name)
    PInteger i     -> shows i
    PFloat f       -> shows f
    PBoolean b     -> shows b
    PString s      -> showString (show s)
    PParen a       -> showParen True $ shows (LillyExprP a shwCtx) 
    PArray as@(_:_)     
      -> showString "[" 
      . foldr (\x acc -> shows (LillyExprP x shwCtx) . showString ", " . acc) 
              (shows . flip LillyExprP shwCtx $ l) hs . showString "]"
      where Just (hs,l) = unsnoc as
    PArray []      -> showString "[]"
    PDefer a       -> showChar '\'' . shows (LillyExprP a shwCtx) . showChar '\''
    PCall f (x:xs) -> showParen (p > 10)
      $ showsPrec 11 (LillyExprP f shwCtx)
      . foldr (\x acc ->  showParen True (shows . flip LillyExprP shwCtx $ x) . showString " " . acc)
              (showParen True (shows . flip LillyExprP shwCtx $ l)) hs
      where Just (hs,l) =  unsnoc (x:xs)
    PCall f []     -> showsPrec 11 (LillyExprP f shwCtx) . showString "()"
    PInfix l op r -> case Map.lookup op (precedenceTable shwCtx) of 
      Just (InfixL, n)  -> showsInfixL p n op (LillyExprP l shwCtx) (LillyExprP r shwCtx)
      Just (InfixR, n) -> showsInfixR p n op (LillyExprP l shwCtx) (LillyExprP r shwCtx)
      Just (InfixN, n)  -> showsInfix p n op (LillyExprP l shwCtx) (LillyExprP r shwCtx)
      Nothing              -> error $ "Operator " <> show op <> " not found in precedence table."
    _ -> undefined

initialShowCtx :: ShowCtx
initialShowCtx = ShowCtx
  { precedenceTable = Map.fromList
      [ ("+", (InfixL, 6))
      , ("-", (InfixL, 6))
      , ("*", (InfixL, 7))
      , ("/", (InfixL, 7))
      , ("%", (InfixL, 7))
      , ("^", (InfixR, 8))
      , ("&&", (InfixL, 3))
      , ("||", (InfixL, 2))
      , ("==", (InfixN, 4))
      , ("<>", (InfixN, 4))
      ]
  }