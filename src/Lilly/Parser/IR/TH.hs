{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE OverloadedStrings   #-}

{-|
Module      : Lilly.Parser.IR.TH
Description : TH Code that generates the Pattern Synonyms for the IR.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.IR.TH
    ( genOpPattern
    , genOpPatterns
    , stdTable
    ) where

import Language.Haskell.TH hiding (Guard)
import Control.Monad (replicateM)
import Lilly.Parser.IR.IR 


-----------------------------
-- Claude TH Cuz TH sucks
-----------------------------

-- | genOpPattern "If" "if" 3 generates:
--
-- pattern PIf :: Expression -> Expression -> Expression -> Expression
-- pattern PIf cond thenExpr elseExpr
--   <- Expression (PCall (Expression (PVariable "if")) [cond, thenExpr, elseExpr])
--     where
--         PIf cond thenExpr elseExpr =
--           Expression (PCall (Expression (PVariable "if")) [cond, thenExpr, elseExpr])
--
-- genOpPattern "Minus1" "minus" 2 gives back the binary case,
-- genOpPattern "Neg1" "neg" 1 the unary case, etc.
genOpPattern :: String -> String -> Int -> Q [Dec]
genOpPattern name ops arity
    | arity < 0 = fail "genOpPattern: arity must be non-negative"
    | otherwise = do
        let patName = mkName ("P" ++ name)

        argNames <- replicateM arity (newName "arg")

        exprTy <- [t| Expression |]
        let sigTy = foldr (\_ acc -> AppT (AppT ArrowT exprTy) acc) exprTy argNames

            -- Expression (PVariable ops)
            varPat  = ConP 'Expression [] [ConP 'PVariable [] [LitP (StringL ops)]]
            varExpr = AppE (ConE 'Expression) (AppE (ConE 'PVariable) (LitE (StringL ops)))

            -- Expression (PCall <varPat/varExpr> [args...])
            matchPat =
              ConP 'Expression []
                [ ConP 'PCall []
                    [ varPat
                    , ListP (map VarP argNames)
                    ]
                ]

            conExpr =
              AppE (ConE 'Expression)
                   (AppE (AppE (ConE 'PCall) varExpr)
                         (ListE (map VarE argNames)))

            sigD'    = PatSynSigD patName sigTy
            clauseD = Clause (map VarP argNames) (NormalB conExpr) []
            patD    = PatSynD patName
                              (PrefixPatSyn argNames)
                              (ExplBidir [clauseD])
                              matchPat

        pure [sigD', patD]

-- | Batch version: genOpPatterns [("If","if",3), ("Minus1","minus",2)]
genOpPatterns :: [(String, String, Int)] -> Q [Dec]
genOpPatterns = fmap concat . traverse (\(n, o, a) -> genOpPattern n o a)
-- End of Claude0

-- | Standard Library Table of ``(pattern name suffix, function name, arity)``.
stdTable :: [(String,String,Int)]
stdTable =
    [ ("If","if",3)
    -- relational operators
    , ("LT1","lt",2)
    , ("LT","<",2)
    , ("GT",">",2)
    , ("LE","<=",2)
    , ("GE",">=",2)
    , ("EQ","==",2)
    , ("NE","<>",2)
    -- Boolean operators
    , ("And","&&",2)
    , ("Or","||",2)
    , ("Not","~",1)
    -- arithmetic operators
    , ("Plus","+",2)
    , ("Minus","-",2)
    , ("Neg","-",1)
    , ("Times","*",2)
    , ("Divide","/",2)
    , ("Power","^",2)
    , ("Mod","%",2)
    -- String operators
    , ("Concat","++",2)
    -- Random
    , ("Random","random",1)
    -- Magic
    , ("Formula","formula",1)
    -- Floating point operators
    , ("Floor","floor",1)
    , ("Ceil","ceil",1)
    , ("Round","round",1)
    , ("Sin","sin",1)
    , ("Cos","cos",1)
    , ("Tan","tan",1)
    , ("ASin","asin",1)
    , ("ACos","acos",1)
    , ("ATan","atan",1)
    , ("Log","log",1)
    -- Tuples
    , ("Fst","fst",1)
    , ("Snd","snd",1)
    , ("Fst1","_1",1)
    , ("Snd1","_2",1)
    -- vectors and arrays 
    , ("Dim", "dim",1)
    , ("Matrix", "matrix",3)
    , ("Cons", "cons",2)
    , ("Length", "length",1)
    , ("Vector", "vector",2)
    ]