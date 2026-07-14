{-|
Module      : Lilly.Parser.New.TH
Description : TH Code that generates the Pattern Synonyms for the decorated IR.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.New.TH where

import Language.Haskell.TH


----------------------------------------------
-- Claude Code cuz TH sucks and breaks 
-- every major version change of GHC
-- (damn you meta-programming).
----------------------------------------------

conP' :: Name -> [Pat] -> Pat
conP' n = ConP n []

{- | 
    a call @genInfixPatSyn "Add" "+"@ will generate a pattern synonym like this:

    @@
    
    @@
-}
genInfixPatSyn :: String -> String -> Q [Dec]
genInfixPatSyn name op = do
  let patName     = mkName ("PP" ++ name)
      leftName    = mkName "left"
      rightName   = mkName "right"
      linfoName   = mkName "linfo"
      rinfoName   = mkName "rinfo"
      newInfoName = mkName "newInfo"

      expressionPName = mkName "ExpressionP"
      pInfixName      = mkName "PInfix"
      consName        = mkName ":<"
      infoConsName    = mkName ":<:"
      toName          = mkName "to"
      irTokenInfoName = mkName "IRTokenInfo"
      tokenStartName  = mkName "tokenStart"
      tokenEndName    = mkName "tokenEnd"

      expT  = ConT expressionPName
      sigTy = ArrowT `AppT` expT `AppT` (ArrowT `AppT` expT `AppT` expT)

      -- Matching side:
      --   ExpressionP ( _ :< PInfix (to -> left) op (to -> right) )
      matchPat =
        conP' expressionPName
          [ InfixP
              WildP
              consName
              ( conP' pInfixName
                  [ ViewP (VarE toName) (VarP leftName)
                  , LitP (StringL op)
                  , ViewP (VarE toName) (VarP rightName)
                  ]
              )
          ]

      -- Builder args: left@(linfo :<: _), right@(rinfo :<: _)
      leftArgPat  = AsP leftName  (InfixP (VarP linfoName) infoConsName WildP)
      rightArgPat = AsP rightName (InfixP (VarP rinfoName) infoConsName WildP)

      -- newInfo = IRTokenInfo (tokenStart linfo) (tokenEnd rinfo)
      newInfoExpr =
        AppE (AppE (ConE irTokenInfoName)
                    (AppE (VarE tokenStartName) (VarE linfoName)))
             (AppE (VarE tokenEndName) (VarE rinfoName))

      -- ExpressionP $ newInfo :< PInfix (to left) op (to right)
      builtExpr =
        AppE (ConE expressionPName)
          ( InfixE
              (Just (VarE newInfoName))
              (ConE consName)
              (Just
                 (AppE
                    (AppE
                       (AppE (ConE pInfixName) (AppE (VarE toName) (VarE leftName)))
                       (LitE (StringL op)))
                    (AppE (VarE toName) (VarE rightName))
                 )
              )
          )

      builderBody =
        LetE [ValD (VarP newInfoName) (NormalB newInfoExpr) []] builtExpr

      builderClause = Clause [leftArgPat, rightArgPat] (NormalB builderBody) []

  pure
    [ PatSynSigD patName sigTy
    , PatSynD patName
        (PrefixPatSyn [leftName, rightName])
        (ExplBidir [builderClause])
        matchPat
    ]

genInfixPatSyns :: [(String, String)] -> Q [Dec]
genInfixPatSyns = fmap concat . traverse (uncurry genInfixPatSyn)

patternTable :: [(String, String)]
patternTable =
  [ -- Arithmetic
    ("Add", "+")
  , ("Sub", "-")
  , ("Mul", "*")
  , ("Div", "/")
  , ("Mod", "%")
  , ("Pow", "^")
    -- Relational
  , ("Lt", "<")
  , ("Gt", ">")
  , ("Leq", "<=")
  , ("Geq", ">=")
  , ("Eq", "=")
  , ("Neq", "<>")
  -- Logical 
  , ("And", "&&")
  , ("Or", "||")
  -- String
  , ("Concat", "++")
  ]