{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Zilly.Classic1.Parser
Description : A Parser for Lilly
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX
-}
module Zilly.Unsugared.Parser where

import Zilly.Unsugared.Parsing.Utilities hiding (type(<))
import Zilly.Unsugared.Parsing.Utilities qualified as PU
import Parser.Numbers

import Text.Parsec hiding (token, (<|>))


import Data.String (IsString(..))
import Control.Monad

import Data.Functor.Identity
import Control.Applicative hiding (optional)
import GHC.TypeLits.Singletons
import Prelude.Singletons
import Data.Kind (Type)
import Data.Functor
import Zilly.Unsugared.Newtypes qualified as T
import Data.Singletons.TH
import Data.Singletons.Decide (decideEquality)
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace (trace)
import GHC.TypeLits (sameNat)
import Data.Text qualified as Text
import Data.Matchers

traceSingI :: forall {k} (n :: k) a. (SingKind k, Show (Demote k), SingI n) => a -> a
traceSingI a = trace (show $ demote @n) a

------------------------
-- Reserved strings
------------------------

-- | Keywords for Lilly
keywords :: [String]
keywords = stdLib ++
  [ "if"
  , "lazy"
  , "Z"
  , "fn"
  , "λ"
  ]

-- | standard library for Lilly
stdLib :: [String]
stdLib =
  [
  ]

-- | Reserved (expression/type) operators
reservedOperators :: [String]
reservedOperators =
  [ ":="
  , "->"
  , "=>"
  ]

----------------------------
-- Parser definition
----------------------------

data ParserState = PST
  { pstIdent      :: Natural
  , insideComment :: Bool
  }

initialPST :: ParserState
initialPST = PST {pstIdent=0,insideComment=False}

type Parser a = ParsecT String ParserState Identity a

-------------------------------
-- Useful Orphans
-------------------------------

instance u ~ () => IsString (Parser u ) where
  fromString str
    | str `elem` keywords = keyword str
    | str `elem` reservedOperators
      = token (string str *> notFollowedBy (choice $ (void . string) <$> ["+","-","=","<",">","%","^",":"]) )
    | otherwise           = void $ token (string str)


-------------------------------
-- Main combinators
-------------------------------

anyKeyword :: Parser ()
anyKeyword = choice $ fmap keyword keywords

---------------------------
-- Book-keeping.
---------------------------

data BookeepInfo = BI
  { tokenPos   :: SourcePos
  , identLevel :: Natural
  }

mkBookeepInfo :: Parser BookeepInfo
mkBookeepInfo = BI <$> getPosition <*> fmap pstIdent getState

----------------------------
-- Aux structures
----------------------------

data Exists f where
  MkExists :: forall f (n :: Natural). SingI n => f n -> Exists f

-----------------------------------------
-- Type Parsers
-----------------------------------------

-- | Parser tree for types. Indexed by the precedence and a context
data family TPrec (ctx :: Type) (n :: Natural)

type Inf     = 0xffffffffffffffff

-- | Precedence of atoms. Defined as Infinity since
-- they have the highest precedence.
type Atom    = Inf

-- | One level bellow atom precedence. Needed to be defined as
-- a constant due to restrictions on type family evaluation inside GADTs.
type PredInf = 0xfffffffffffffffe

type PrefixPrec = 0xfffffffffffffffd

type PostfixPrec = 0xfffffffffffffffe


-- | Expressions Have the lowest precedence.
type Expr ctx  = EPrec ctx 0

-- | A type in lilly, is a type of precedence 0.
type Types ctx = TPrec ctx 0

data ParsingStage

------------------------------
-- Precedence Inf Types
------------------------------


data instance TPrec ctx Atom where
  -- | Integers: @Z@, @int@
  TZ         :: TZX ctx -> TPrec ctx Atom
  -- | Variables: any valid identifier
  TVar       :: TVX ctx -> String             -> TPrec ctx Atom
  -- | Tuples @(A,B)@
  TTuple     :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TTX ctx -> TPrec ctx n -> TPrec ctx n -> TPrec ctx Atom
  -- | Parentheses: @(type)@
  TParen     :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TPX ctx -> TPrec ctx n -> TPrec ctx Atom
 -- | Invisible Lazy type: @lazy@
  TLazySp      :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TLSPX ctx -> TPrec ctx n -> TPrec ctx Atom

type family TZX (ctx :: Type)    :: Type
type family TFX (ctx :: Type)    :: Type
type family TVX (ctx :: Type)    :: Type
type family TTX (ctx :: Type)    :: Type
type family TPX (ctx :: Type)    :: Type
type family TLSPX (ctx :: Type)  :: Type

type instance TZX ParsingStage    = BookeepInfo
type instance TFX ParsingStage    = BookeepInfo
type instance TVX ParsingStage    = BookeepInfo
type instance TTX ParsingStage    = BookeepInfo
type instance TPX ParsingStage    = BookeepInfo
type instance TLSPX ParsingStage  = BookeepInfo



mkZT :: Parser (TPrec ParsingStage Inf)
mkZT = mkBookeepInfo <**> (TZ <$ "Z")


mkVarT ::  Parser (String -> TPrec ParsingStage Inf)
mkVarT = TVar <$> mkBookeepInfo

mkParenOrTupleT :: forall {n0} n. (SingI n, n0 ~ Inf, (n < n0) ~ True)
  => Parser (TPrec ParsingStage n -> Maybe (TPrec ParsingStage n) -> TPrec ParsingStage n0)
mkParenOrTupleT = f <$> mkBookeepInfo
  where
    f :: BookeepInfo -> TPrec ParsingStage n -> Maybe (TPrec ParsingStage n) -> TPrec ParsingStage n0
    f bk a = \case
      Just b -> TTuple bk a b
      Nothing -> TParen bk a

mkLazySpT :: forall n0. (SingI n0, (n0 < Atom) ~ True)
  => Parser (TPrec ParsingStage n0 -> TPrec ParsingStage Atom)
mkLazySpT =  TLazySp <$> mkBookeepInfo




pTypeAtom :: Parser (TPrec ParsingStage Atom)
pTypeAtom
  =   mkZT
  <|> (mkLazySpT  <* "lazy") <*> bracketed pTypes
  <|> parens (mkParenOrTupleT <*> pTypes <*> optionMaybe ("," *> pTypes) )
  <|> mkVarT <*> ident

instance (SingI n',SingI n, (n' > n) ~ True) => TPrec ctx n' PU.< TPrec ctx n where
  upcast = case sing @n of
    SNat @n'' -> case sameNat (SNat @n'') (SNat @0) of
      Just Refl     -> OfHigherTPrec0
      Nothing -> error "TPrec can only be one of the following: Inf-1, 0."
  downcast t
    = withKnownNat (sing @n)
    $ withKnownNat (sing @n')
    $ case decideEquality (sing @n) (SNat @0) of
      Just Refl     -> case t of
        OfHigherTPrec0 @x f -> withKnownNat (sing @x) $ case sCompare' @n' @x of
          EQ' -> withEqRefl @n' @x $ Just f
          LT' -> Just $ upcast  @(TPrec ctx x) @(TPrec ctx n') f
          GT' -> downcast @(TPrec ctx n') @(TPrec ctx x) f
        _ -> Nothing
      Nothing -> error "TPrec can only be one of the following: 0."

data Ordering' a b where
  EQ' :: forall a b. ((a == b) ~ True, (b == a) ~ True) => Ordering' a b
  LT' :: forall a b. ((a <  b) ~ True, (b > a ) ~ True) => Ordering' a b
  GT' :: forall a b. ((a >  b) ~ True, (b < a ) ~ True) => Ordering' a b

sCompare' :: forall {k} (a :: k) (b :: k). (SOrd k, SingI a, SingI b) => Ordering' a b
sCompare' = case (sing @a %== sing @b, sing @a %< sing @b, sing @a %> sing @b) of
  (STrue,_,_) -> downEQ' @a @b $ EQ'
  (_,STrue,_) -> downLT' @a @b $ LT'
  (_,_,STrue) -> downGT' @a @b $ GT'
  _           -> error "impossible case. SOrd imposes a total order."

downLT' :: forall {k} (a :: k) (b :: k) r. (SOrd k, SingI a, SingI b, (a < b) ~ True) => (( (b > a) ~ True) => r) -> r
downLT' f = case sing @b %> sing @a  of
    STrue  -> f
    SFalse -> error "error in reversing LT'"

downGT' :: forall {k} (a :: k) (b :: k) r. (SOrd k, SingI a, SingI b, (a > b) ~ True) => (( (b < a) ~ True) => r) -> r
downGT' f = case sing @b %< sing @a  of
    STrue  -> f
    SFalse -> error "error in reversing GT'"

downEQ' :: forall {k} (a :: k) (b :: k) r. (SOrd k, SingI a, SingI b, (a == b) ~ True) => (( (b == a) ~ True) => r) -> r
downEQ' f = case sing @b %== sing @a  of
    STrue  -> f
    SFalse -> error "error in reversing EQ'"


eqToRefl :: (a == b) ~ True => a :~: b
eqToRefl = unsafeCoerce trivialRefl

trivialRefl :: () :~: ()
trivialRefl = Refl

withEqRefl :: forall a b r. (a == b) ~ True => ((a ~ b) => r) -> r
withEqRefl f = case eqToRefl @a @b of
  Refl -> f

--
-- ------------------------------
-- -- Precedence 0 Types
-- ------------------------------
--
data instance TPrec ctx 0 where
  -- | Lowest precedence type. Visible Type application
  TArrow :: forall n ctx. (SingI n, (n > 0) ~ True )
    => TARX ctx -> TPrec ctx n -> TPrec ctx 0 -> TPrec ctx 0
  OfHigherTPrec0 :: forall n ctx. (SingI n,(n > 0) ~ True )
    => TPrec ctx n -> TPrec ctx 0

type family TARX (ctx :: Type) :: Type
type instance TARX ParsingStage = BookeepInfo

mkArrowT :: forall {n0} n. (SingI n, n0 ~ 0, (n > n0) ~ True)
  => Parser (TPrec ParsingStage n -> TPrec ParsingStage 0 -> TPrec ParsingStage 0)
mkArrowT = TArrow <$> mkBookeepInfo
--
--
pTypes :: Parser (Types ParsingStage)
pTypes = precedence $
  sops InfixR  [mkArrowT <* "=>"] |-<
  Atom pTypeAtom

t2NT :: forall n ctx. (SingI n) => TPrec ctx n-> T.Types
t2NT f = case sing @n of
  SNat -> case (sameNat (SNat @n) (SNat @0), sameNat (SNat @n) (SNat @Atom)) of
    (Just Refl,_) -> case f of
      OfHigherTPrec0 f' -> t2NT f'
      TArrow _ a b -> t2NT a T.:-> t2NT b
    (_,Just Refl) -> case f of
      TZ _ -> T.Z
      TVar _ v  -> T.TVar (T.TV $ Text.pack v)
      TTuple _ a b -> T.Tuple (t2NT a) (t2NT b)
      TParen _ a   -> t2NT a
      TLazySp _ a  -> T.Lazy $ t2NT a
    _             -> error "Type precedence must be one of: Atom, 0."

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

-- | Expression parse trees are types indexed by its precedence.
data family EPrec (ctx :: Type) (n :: Natural)

------------------------------
-- Precedence Inf Expressions
------------------------------

-- | Expression trees for attoms
data instance EPrec ctx Atom where
  -- | Integers @-1,2,3,-100,....@
  PInt     :: EIX ctx -> Int    -> EPrec ctx Atom
  -- | Variables: any identifier
  PVar     :: EVX ctx  -> String -> EPrec ctx Atom
  -- | Tuples @(expr,expr)@
  PTuple   :: forall n ctx. (SingI n,(n < Atom) ~ True)
    => ETX ctx -> EPrec ctx n -> EPrec ctx n -> EPrec ctx Atom
  -- | parenthesis: @(expr)@
  PParen   :: forall n ctx. (SingI n,(n < Atom) ~ True)
    => EPX ctx -> EPrec ctx n    -> EPrec ctx Atom
  -- | Quoted expressions: @'expr'@
  PDefer   :: forall n ctx. (SingI n,(n < Atom) ~ True)
    => EDefX ctx -> EPrec ctx n    -> EPrec ctx Atom
  -- | If function: @if(expr,expr,expr)@
  PIf :: forall n0 n1 n2 ctx.
    ( (n0 < Atom) ~ True
    , (n1 < Atom) ~ True
    , (n2 < Atom) ~ True
    , SingI n0
    , SingI n1
    , SingI n2
    )
    => EIfX ctx
    -> (EPrec ctx n0, EPrec ctx n1, EPrec ctx n2)
    -> EPrec ctx Atom

type family EIX (ctx :: Type) :: Type
type family EVX (ctx :: Type) :: Type
type family ETX (ctx :: Type) :: Type
type family EPX (ctx :: Type) :: Type
type family EDefX (ctx :: Type) :: Type
type family EIfX (ctx :: Type) :: Type


type instance EIX ParsingStage = BookeepInfo
type instance EVX ParsingStage = BookeepInfo
type instance ETX ParsingStage = BookeepInfo
type instance EPX ParsingStage = BookeepInfo
type instance EDefX ParsingStage = BookeepInfo
type instance EIfX ParsingStage = BookeepInfo



mkIf :: forall {n} n0 n1 n2.
  ( n ~ Atom
  , SingI n0
  , SingI n1
  , SingI n2
  , (n0 < n) ~ True
  , (n1 < n) ~ True
  , (n2 < n) ~ True
  ) => Parser (EPrec ParsingStage n0, EPrec ParsingStage n1, EPrec ParsingStage n2) -> Parser (EPrec ParsingStage Atom)
mkIf p = "if" *> parens (PIf <$> mkBookeepInfo <*> p)

ident :: Parser String
ident = mkIdent anyKeyword


mkInt :: forall {n0}. (n0 ~ Atom)
  =>  Parser (Int -> EPrec ParsingStage n0)
mkInt = PInt <$> mkBookeepInfo

mkVar :: forall {n0}. (n0 ~ Atom)
  =>  Parser (String -> EPrec ParsingStage n0)
mkVar = PVar <$> mkBookeepInfo

mkParen :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True)
  =>  Parser (EPrec ParsingStage n) -> Parser (EPrec ParsingStage n0)
mkParen p = parens $ PParen <$> mkBookeepInfo <*> p


mkParenOrTupleP :: forall {n0} n. (SingI n, n0 ~ Inf, (n < n0) ~ True)
  => Parser (EPrec ParsingStage n -> Maybe (EPrec ParsingStage n) -> EPrec ParsingStage n0)
mkParenOrTupleP = f <$> mkBookeepInfo
  where
    f :: BookeepInfo -> EPrec ParsingStage n -> Maybe (EPrec ParsingStage n) -> EPrec ParsingStage n0
    f bk a = \case
      Just b -> PTuple bk a b
      Nothing -> PParen bk a


mkDefer :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True)
  =>  Parser (EPrec ParsingStage n) -> Parser (EPrec ParsingStage n0)
mkDefer p = quoted $ PDefer <$> mkBookeepInfo <*> p

atom :: Parser (EPrec ParsingStage Atom)
atom
  = pNumber
  <|> mkDefer expr
  <|> mkIf ((,,) <$> (expr <* ",")  <*> (expr <* ",") <*> expr)
  <|> parens (mkParenOrTupleP <*> expr <*> optionMaybe ("," *> expr))
  <|> mkVar    <*> ident
  where
    f (Just _) as = read  @Int $ '-' : as
    f Nothing  as = read @Int as
    pNumber'
      =  mkInt <*> (f <$> optionMaybe "-" <*> many1 digit <* notFollowedBy (digit <|> char '.'))
      <?> "malformed integer literal"

    pNumber = pNumber' <* spaces

-----------------------------------
-- Precedence AppPrec Expressions
-----------------------------------

data instance EPrec ctx PrefixPrec where
  PUMinus :: EUMX ctx -> EPrec ctx PrefixPrec -> EPrec ctx PrefixPrec
  OfHigherPrefixPrec :: forall n ctx. (SingI n,(n > PrefixPrec) ~ True)
    => EPrec ctx n -> EPrec ctx PrefixPrec

type family EUMX (ctx :: Type) :: Type
type instance EUMX ParsingStage = BookeepInfo

mkUMinus :: Parser (EPrec ParsingStage PrefixPrec -> EPrec ParsingStage PrefixPrec)
mkUMinus = PUMinus <$> mkBookeepInfo

data instance EPrec ctx PostfixPrec where
  -- Function applications: @expr(expr00,expr01,....)(expr10,expr11,...)...@
  PApp    :: EAppX ctx -> EPrec ctx PostfixPrec -> EPrec ctx 0 -> EPrec ctx PostfixPrec
  OfHigherPostfixPrec :: forall n ctx. (SingI n,(n > PostfixPrec) ~ True)
    => EPrec ctx n -> EPrec ctx PostfixPrec

type family EAppX (ctx :: Type)  :: Type

type instance EAppX ParsingStage = BookeepInfo

mkApp :: Parser (EPrec ParsingStage 0) -> Parser (EPrec ParsingStage PostfixPrec -> EPrec ParsingStage PostfixPrec)
mkApp p =  (\p' x y -> PApp p' y x ) <$> mkBookeepInfo <*> parens p

------------------------------
-- Precedence 0 Expressions
------------------------------

data instance EPrec ctx 1 where
-- | Lambda functions:
  -- @
  --  fn(type0 var0) => return_type -> expr
  --  fn(type0 var0) -> expr
  -- @
  PLambda
    :: ELambdaX ctx
    -> (EPrec ctx 0, T.Types)
    -> Maybe T.Types
    -> EPrec ctx 1
    -> EPrec ctx 1
  OfHigher1 :: forall n ctx. (SingI n,(n > 1) ~ True) => EPrec ctx n -> EPrec ctx 1

type family ELambdaX (ctx :: Type) :: Type
type instance ELambdaX ParsingStage = BookeepInfo


mkLambda :: Parser (EPrec ParsingStage 1 -> EPrec ParsingStage 1)
mkLambda
  = (PLambda
  <$> (mkBookeepInfo <* ("fn" <|> "λ") )
  <*> parens (liftA2 (\t e -> (e,t2NT t)) pTypes expr)
  <*> optionMaybe ("=>" *> fmap t2NT pTypes) )
  <* "->"

------------------------------
-- Precedence 0 Expressions
------------------------------



-- | Expressions.
data instance EPrec ctx 0 where
  OfHigher0 :: forall n ctx. (SingI n, (n > 0) ~ True) => EPrec ctx n -> EPrec ctx 0

expr :: Parser (EPrec ParsingStage 0)
expr = fmap OfHigher0 . precedence $
  sops Prefix [mkLambda] |-<
  sops Postfix
    [ mkApp    expr
    ] |-<

  Atom atom

instance (SingI n', SingI n, (n' > n) ~ True) => EPrec ctx n' PU.< EPrec ctx n where
  upcast = case () of
    _ | Just Refl <- matches @0 (sing @n) -> OfHigher0
    _ | Just Refl <- matches @1 (sing @n) -> OfHigher1
    _ | Just Refl <- matches @PostfixPrec (sing @n) -> OfHigherPostfixPrec
    _ | Just Refl <- matches @PrefixPrec (sing @n) -> OfHigherPrefixPrec
    _ -> error "Error. Upcast Expression Precedences must be one of: 0,1,4,6,7,8,Postfix,Prefix."
  downcast t
    = withKnownNat (sing @n')
    $ withKnownNat (sing @n)
    $ case () of
      _ | Just Refl <- matches @0 (sing @n) -> case t of
        OfHigher0 f -> genericDowncast f
      _ | Just Refl <- matches @1 (sing @n) -> case t of
        OfHigher1 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @PostfixPrec (sing @n) -> case t of
        OfHigherPostfixPrec f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @PrefixPrec (sing @n) -> case t of
        OfHigherPrefixPrec f -> genericDowncast f
        _           -> Nothing
      _ -> error "Error. Downcast Expression Precedences must be one of: 0,1,4,6,7,8,Postfix,Prefix."
    where
      genericDowncast :: forall x. (SingI x)
        =>  EPrec ctx x -> Maybe (EPrec ctx n')
      genericDowncast f = withKnownNat (sing @x) $ case sCompare' @n' @x of
          EQ' -> withEqRefl @n' @x $ Just f
          LT' -> Just $ upcast  @(EPrec ctx x) @(EPrec ctx n') f
          GT' -> downcast @(EPrec ctx n') @(EPrec ctx x) f

-----------------------------------------
-- Action Grammar
-----------------------------------------

data A1 ctx
  = Seq (ASeqX ctx) (A0 ctx) [A0 ctx]
  | OfA0 (A0 ctx)

type family ASeqX (ctx :: Type) :: Type

type instance ASeqX ParsingStage = Void

pattern MkSeq :: A0 ctx -> [A0 ctx] -> A1 ctx
pattern MkSeq b bs <-  Seq _ b bs
  where MkSeq b bs = Seq undefined b bs

data A0 ctx
  = Decl T.Types (Expr ctx) (Expr ctx) (ADeclX ctx)
  | Assign (Expr ctx) (Expr ctx)     (AAssignX ctx)
  | Print (Expr ctx)           (APrintX ctx)
  | SysCommand String (SysCommandX ctx)

type family ADeclX      (ctx :: Type) :: Type
type family AAssignX    (ctx :: Type) :: Type
type family APrintX     (ctx :: Type) :: Type
type family SysCommandX (ctx :: Type) :: Type

type instance ADeclX     ParsingStage   = BookeepInfo
type instance AAssignX    ParsingStage  = BookeepInfo
type instance APrintX     ParsingStage  = BookeepInfo
type instance SysCommandX ParsingStage  = BookeepInfo

instance A0 ctx PU.< A1 ctx where
  upcast = OfA0
  downcast t = case t of
    OfA0 t' -> Just t'
    _       -> Nothing



mkDecl :: Parser T.Types -> Parser (Expr ParsingStage) -> Parser (Expr ParsingStage) -> Parser (A0 ParsingStage)
mkDecl pType' ident' expr'
  = mkBookeepInfo <**> (Decl <$> pType' <*> ident' <* ":=" <*> expr')

mkAssign :: Parser (Expr ParsingStage) -> Parser (Expr ParsingStage) -> Parser (A0 ParsingStage)
mkAssign ident' expr' = mkBookeepInfo <**> (Assign <$> ident' <*  ":=" <*> expr')

mkSysCommand :: Parser (A0 ParsingStage)
mkSysCommand = special <|> normal
  where
    special :: Parser (A0 ParsingStage)
    special = mkBookeepInfo <**> ("." $> SysCommand "reset")
    normal :: Parser (A0 ParsingStage)
    normal  = mkBookeepInfo <**> (token $ string "sys." $> SysCommand <*> ident <* optional "()" <* optional ";")

a0 :: Parser (A0 ParsingStage)
a0
  =   mkSysCommand
  <|> flip Print <$> mkBookeepInfo <*> try (fully expr)
  <|> try (mkDecl (t2NT <$> pTypes) expr expr)
  <|> mkAssign expr expr

a0' :: Parser (A0 ParsingStage)
a0' = a0
action :: Parser (A0 ParsingStage)
action =  a0 <* optional (lexeme (string ";"))

action' :: Parser (A0 ParsingStage)
action' =  a0' <* optional (lexeme (string ";"))


-----------------------------------------
-- File Parsing
-----------------------------------------

parseFile' :: FilePath -> IO (Either ParseError (A1 ParsingStage))
parseFile' fp = readFile fp >>= \c -> do
  let c' = lines c
  let as =  traverse (runParser (spaces *> action') initialPST "") c'
  case as of
    Right []     -> pure . Right . OfA0 $ Print (OfHigher0 $ PInt undefined 0) undefined
    Right (x:xs) -> pure . Right $ Seq undefined x xs
    Left e       -> pure . Left $ e

-----------------------------------------
-- Run parser
-----------------------------------------

parseExpr :: String -> String
parseExpr s = case runParser (spaces *> fully expr) initialPST "" s of
  Left e -> show e
  Right _ -> "success!"

parseTypes :: String -> String
parseTypes s = case runParser (spaces *> fully pTypes) initialPST "" s of
  Left e -> show e
  Right _ -> "success!"

parseAction :: String -> String
parseAction s = case runParser (spaces *> fully action) initialPST "" s of
  Left e -> show e
  Right _ -> "success!"

parseAction' :: String -> Either ParseError (A1 ParsingStage)
parseAction' s = case runParser (spaces *> fully action') initialPST "" s of
  Left e -> Left e
  Right a -> Right $ OfA0 a


yieldVarName :: forall n ctx. SingI n => EPrec ctx n -> Maybe String
yieldVarName x | Just Refl <- matches @0 (sing @n) = case x of
  OfHigher0 x' -> yieldVarName x'
yieldVarName x | Just Refl <- matches @1 (sing @n) = case x of
  OfHigher1 x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @PostfixPrec (sing @n) = case x of
  OfHigherPostfixPrec x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @PrefixPrec (sing @n) = case x of
  OfHigherPrefixPrec x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @Atom (sing @n) = case x of
  PVar _ s -> Just s
  _        -> Nothing
yieldVarName _ = error "Error. Upcast Expression Precedences must be one of: 0,1,Postfix,Prefix."
instance SingI n => Show (TPrec ctx n) where
  showsPrec p  = withKnownNat (sing @n) $ case (sameNat (sing @n) (SNat @Atom), sameNat (sing @n) (SNat @0)) of
    (Just Refl,_) -> \case
      TZ _ -> showString "Z"
      TVar _ s -> showString s
      TTuple _ a b -> showString "(" . shows a . showString ", " . shows b . showString ")"
      TParen _ a -> showString "(" . shows a . showString ")"
      TLazySp _ a -> showString "Lazy<" . shows a . showString ">"
    (_, Just Refl) -> \case
      OfHigherTPrec0 a -> shows a
      TArrow _ a b -> showParen (p > 0) $ shows a . showString " => " . shows b
    _ -> const $ showString "Precedence not defined"


instance SingI n => Show (EPrec ctx n) where

  showsPrec p = withKnownNat (sing @n) $ case
      ( sameNat (SNat @n) (SNat @0)
      , sameNat (SNat @n) (SNat @1)
      , sameNat (SNat @n) (SNat @PostfixPrec)
      , sameNat (SNat @n) (SNat @Atom)
      ) of
      (Just Refl,_,_,_) -> \case
        OfHigher0 e -> showsPrec p e
      (_,Just Refl,_,_) -> \case
        PLambda _ (x,t) mt e -> showParen (p > 1)
          $ showString "λ(" . shows t . showString " "
          . shows x . (maybe (showString "") $ \s -> showString " => " . shows s) mt
          . showString " -> "
          . shows e
        OfHigher1 x -> showsPrec p x
      (_,_,Just Refl,_) -> \case
        PApp _ f x -> showParen (p > 10)
          $ showsPrec 11 f
          . showParen True (shows x)
        OfHigherPostfixPrec a  -> showsPrec p a
      (_,_,_,Just Refl) -> \case
        PInt _ n -> shows n
        PVar _ n -> showString n
        PTuple _ a b -> showString "(" . shows a . showString ", " . shows b . showString ")"
        PParen _ a -> showParen True $ shows a
        PDefer _ a -> showString "\"" . shows a . showString "\""
        PIf _ (a, b, c)
          -> showString "if(" . shows a . showString ", " . shows b
          . showString ", " . shows c . showString ")"
      _ -> const $ showString "Precedence not defined"


instance Show (A0 ctx) where
  show (Decl t e e' _) = show t <> " " <> show e <> " := " <> show e' <> ";"
  show (Assign e e' _) = show e <> " := " <> show e' <> ";"
  show (Print e _)     = show e
  show (SysCommand e _) = "sys." <> e <> "();"

instance Show (A1 ctx) where
  show (OfA0 x) = show x
  show (Seq _ x xs) = unlines $ show x : fmap show xs
