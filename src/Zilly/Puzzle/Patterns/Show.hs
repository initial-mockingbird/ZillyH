module Zilly.Puzzle.Patterns.Show
  ( showLPattern
  , showPattern
  , showPatternGuard
  ) where

import Zilly.Puzzle.Patterns.Base


showLPattern :: LPattern ctx -> String
showLPattern (LVar  name) = name
showLPattern (LWild ) = "_"
showLPattern (LInt  n) = show n
showLPattern (LBool  b) = if b then "true" else "false"
showLPattern (LString  s) = show s
showLPattern (LFloat  f) = show f
showLPattern (LTuple  p1 p2 ps) = "(" ++ showLPattern p1 ++ ", " ++ showLPattern p2 ++ concatMap ((", " ++) . showLPattern) ps ++ ")"
showLPattern (LCons  name ps) = name ++ concatMap ((" " ++) . showLPattern) ps
showLPattern (LARecord  fields) = "{" ++ concatMap (\(n, t) -> n ++ " : " ++ show t ++ ", ") fields ++ "}"

showPatternGuard :: (expr -> String) -> PatternGuard expr ctx -> String
showPatternGuard showExpr (ExprGuard  expr) = showExpr expr
showPatternGuard showExpr (BindingGuard  pattern expr) = showLPattern pattern ++ " <- " ++ showExpr expr



showPattern :: (expr -> String) -> Pattern expr ctx -> String
showPattern f (Pattern  lp gs@(_:_))
  = showLPattern lp
  <> " < "
  <> concatMap (\g -> showPatternGuard f g ++ ", ") gs
  <> " > "
showPattern _ (Pattern  lp []) = showLPattern lp
