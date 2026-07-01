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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
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
module Zilly.Puzzle.Parser where

import Parser.Patterns hiding (type(<))
import Parser.Patterns qualified as PU
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
import Zilly.Puzzle.Types.Exports qualified as T
import Data.Singletons.TH
import Data.Singletons.Decide (decideEquality)
import Unsafe.Coerce (unsafeCoerce)
import Debug.Trace (trace)
import GHC.TypeLits (sameNat)
import Data.Text qualified as Text
import Data.Matchers
import Text.Read (readMaybe)
import Data.List (intercalate)
import Debug.Trace (trace)
import Language.Haskell.TH (Q,Dec(..),reifyType,Name)
import Language.Haskell.TH qualified as TH

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
  , "R"
  , "Bool"
  , "String"
  , "fn"
  , "λ"
  , "array"
  , "match"
  , "with"
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
  , ":-"
  , "|"
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
      = token (string str *> notFollowedBy (choice $ (void . string) <$> ["+","-","=","<",">","%","^",":","|"]) )
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

-- data Exists f where
--   MkExists :: forall f (n :: Natural). SingI n => f n -> Exists f

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


type PrefixPrec = 0xfffffffffffffffc

type PostfixPrec = 0xfffffffffffffffd


-- | Expressions Have the lowest precedence.
type Expr ctx  = EPrec ctx 0

-- | A type in lilly, is a type of precedence 0.
type Types ctx = TPrec ctx 0

data ParsingStage

------------------------------
-- Precedence Inf Types
------------------------------

type TCtxMonoW ctx = TNX ctx

type TCtxMono ctx =
  ( TNX ctx ~ TARecordX ctx
  , TNX ctx ~ TARX ctx
  )

tPrecMorphism :: forall ctx ctx' n .
  ( SingI n
  , TCtxMono ctx
  , TCtxMono ctx'
  ) => (TCtxMonoW ctx -> TCtxMonoW ctx') ->  TPrec ctx n -> TPrec ctx' n
tPrecMorphism f = case () of
  () | Just Refl <- matches @Atom (sing @n) -> \case
        TNormal bk name args -> TNormal (f bk) name (tPrecMorphism f <$> args)
        TARecord bk fields  -> TARecord (f bk) [(k, tPrecMorphism f v) | (k,v) <- fields]
        OfLowerTPrec a      -> OfLowerTPrec (tPrecMorphism f a)
     | Just Refl <- matches @0 (sing @n) -> \case
        TArrow bk a b       -> TArrow (f bk) (tPrecMorphism f a) (tPrecMorphism f b)
        OfHigherTPrec0 a    -> OfHigherTPrec0 (tPrecMorphism f a)
     | otherwise -> error "TPrec can only be one of the following: Inf, 0."


data instance TPrec ctx Atom where
  -- | Mimics TCon carrying the book-keeping information.
  TNormal   :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TNX ctx -> String -> [TPrec ctx n] -> TPrec ctx Atom
  TTypeVar   :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TNX ctx -> String -> [TPrec ctx n] -> TPrec ctx Atom
  TInfer   :: forall ctx.
    TNX ctx -> TPrec ctx Atom
  TARecord :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TARecordX ctx -> [(String, TPrec ctx n)] -> TPrec ctx Atom
  OfLowerTPrec :: forall n ctx. (SingI n, (n < Atom) ~ True)
    => TPrec ctx n -> TPrec ctx Atom

type family TARecordX (ctx :: Type) :: Type
type family TNX (ctx :: Type)       :: Type
type instance TNX ParsingStage       = BookeepInfo
type instance TARecordX ParsingStage = BookeepInfo


mkTNormal :: forall n . (SingI n, (n < Atom) ~ True)
    => Parser (String -> [TPrec ParsingStage n] -> TPrec ParsingStage Atom)
mkTNormal = TNormal @n @ParsingStage <$> mkBookeepInfo

mkTTypeVar :: forall n . (SingI n, (n < Atom) ~ True)
    => Parser (String -> [TPrec ParsingStage n] -> TPrec ParsingStage Atom)
mkTTypeVar = TTypeVar @n @ParsingStage <$> mkBookeepInfo

mkTInfer :: Parser (TPrec ParsingStage Atom)
mkTInfer = TInfer @ParsingStage <$> mkBookeepInfo



pARecordT :: Parser (TPrec ParsingStage Atom)
pARecordT = TARecord <$> mkBookeepInfo <*> between "{" "}" (field `sepBy` ",")
  where
    field :: Parser (String, TPrec ParsingStage 0)
    field = (,) <$> (ident <* ":") <*> pTypes

pArrayT :: Parser (TPrec ParsingStage Atom)
pArrayT
  = "array" *>
  ( f
  <$> mkBookeepInfo
  <*> between ("[") ("]") (Text.Parsec.many ",")
  <*> bracketed pTypes
  )
  where
   f ::  TNX ParsingStage -> [a] -> TPrec ParsingStage 0 -> TPrec ParsingStage Atom
   f bk xs x = TNormal @0 @ParsingStage bk "array"
    [ OfHigherTPrec0 $ TNormal @0 @ParsingStage bk (show (1 + length xs)) []
    , x
    ]

pNormal :: Parser (TPrec ParsingStage Atom)
pNormal
  = ("::" *> mkTInfer)
  <|> pArrayT
  <|>
    (mkTTypeVar @0
      <*> (char '\'' >> fmap (mappend "'") ident)
      <*> pure []
    )
  <|>
    (mkTNormal
      <*>  ident
      <*> option [] (bracketed $  pTypes `sepBy` "," )
    )



mkParenOrTupleT :: forall {n0} n. (SingI n, n0 ~ Inf, (n < n0) ~ True)
  => Parser (TPrec ParsingStage n -> [TPrec ParsingStage n] -> TPrec ParsingStage n0)
mkParenOrTupleT = f <$> mkBookeepInfo
  where
    f :: BookeepInfo -> TPrec ParsingStage n -> [TPrec ParsingStage n] -> TPrec ParsingStage n0
    f bk a = \case
      (b:bs) -> TNormal bk "Tuple" (a:b:bs)
      [] -> OfLowerTPrec @n @ParsingStage a

pParenOrTupleT :: Parser (TPrec ParsingStage Atom)
pParenOrTupleT
  = parens (mkParenOrTupleT <*> pTypes <*> option [] ("," *> sepBy pTypes ",") )


pTypeAtom :: Parser (TPrec ParsingStage Atom)
pTypeAtom =  pARecordT <|> pNormal <|> pParenOrTupleT


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
      TNormal _ "lazy" [a] -> T.Lazy (t2NT a)
      TNormal _ a as -> T.TCon (Text.pack a) (t2NT <$> as)
      TTypeVar _ a _ -> T.TVar (T.TV (Text.pack a))
      TInfer _  -> T.ZInfer
      TARecord _ fields -> T.ARecord [(Text.pack k, t2NT v) | (k,v) <- fields]
      OfLowerTPrec f' -> t2NT f'
    _             -> error "Type precedence must be one of: Atom, 0."

-----------------------------------------
-- Expression Grammar / Untyped AST
-----------------------------------------

-- | Expression parse trees are types indexed by its precedence.
data family EPrec (ctx :: Type) (n :: Natural)

------------------------------
-- Precedence Inf Expressions
------------------------------

type ECtxMonoW ctx = EIX ctx

type ECtxMono ctx =
  ( EIX ctx ~ EFX ctx
  , EIX ctx ~ EBX ctx
  , EIX ctx ~ ESX ctx
  , EIX ctx ~ EVX ctx
  , EIX ctx ~ ETX ctx
  , EIX ctx ~ EPX ctx
  , EIX ctx ~ EAX ctx
  , EIX ctx ~ EDefX ctx
  , EIX ctx ~ EIfX ctx
  , EIX ctx ~ EMatchX ctx
  , EIX ctx ~ EECons ctx
  , EIX ctx ~ EARecordX ctx
  , EIX ctx ~ EUMX ctx
  , EIX ctx ~ ENegateX ctx
  , EIX ctx ~ EAppX ctx
  , EIX ctx ~ EAAppX ctx
  , EIX ctx ~ EDAppX ctx
  , EIX ctx ~ EPowX ctx
  , EIX ctx ~ EMulX ctx
  , EIX ctx ~ EDivX ctx
  , EIX ctx ~ EModX ctx
  , EIX ctx ~ EPlusX ctx
  , EIX ctx ~ EMinusX ctx
  , EIX ctx ~ EAppendX ctx
  , EIX ctx ~ EPLTX ctx
  , EIX ctx ~ EPLTEQX ctx
  , EIX ctx ~ EPGTX ctx
  , EIX ctx ~ EPGTEQX ctx
  , EIX ctx ~ EPEQX ctx
  , EIX ctx ~ EPNEQX ctx
  , EIX ctx ~ EAndX ctx
  , EIX ctx ~ EOrX ctx
  , EIX ctx ~ ELambdaX ctx
  )

ePrecMorphism :: forall ctx ctx' n .
  ( SingI n
  , ECtxMono ctx
  , ECtxMono ctx'
  , PatCtxMono ctx
  , PatCtxMono ctx'
  )
  => (ECtxMonoW ctx -> ECtxMonoW ctx')
  -> (PatCtxMonoW ctx -> PatCtxMonoW ctx')
  -> EPrec ctx n
  -> EPrec ctx' n
ePrecMorphism f g = case () of
  () | Just Refl <- matches @Atom (sing @n) -> \case
        PInt bk i         -> PInt (f bk) i
        PFloat bk d       -> PFloat (f bk) d
        PBool bk b        -> PBool (f bk) b
        PString bk s      -> PString (f bk) s
        PVar bk s         -> PVar (f bk) s
        PTuple bk a b bs  -> PTuple (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b) (ePrecMorphism f g <$> bs)
        PParen bk a       -> PParen (f bk) (ePrecMorphism f g a)
        PArray bk xs      -> PArray (f bk) (ePrecMorphism f g <$> xs)
        PDefer bk a       -> PDefer (f bk) (ePrecMorphism f g a)
        PIf bk (a,b,c)   -> PIf (f bk) (ePrecMorphism f g a, ePrecMorphism f g b, ePrecMorphism f g c)
        PMatch bk e bs    -> PMatch (f bk) (ePrecMorphism f g e) [(patPrecMorphism g f p, ePrecMorphism f g v) | (p,v) <- bs]
        PECons bk name xs-> PECons (f bk) name (ePrecMorphism f g <$> xs)
        PEARecord bk fs   -> PEARecord (f bk) [(k, ePrecMorphism f g v) | (k,v) <- fs]
      | Just Refl <- matches @PostfixPrec (sing @n) -> \case
        PApp bk e xs      -> PApp (f bk) (ePrecMorphism f g e) (ePrecMorphism f g <$> xs)
        PAppArr bk e xs   -> PAppArr (f bk) (ePrecMorphism f g e) (f' <$> xs)
          where
          f' (PIndex idx) = PIndex (ePrecMorphism f g idx)
          f' (PRangeIndexer (idx0,idx1))  = PRangeIndexer (ePrecMorphism f g idx0, ePrecMorphism f g idx1)
        PDotApp bk e s    -> PDotApp (f bk) (ePrecMorphism f g e) s
        OfHigherPostfixPrec a -> OfHigherPostfixPrec (ePrecMorphism f g a)
      | Just Refl <- matches @PrefixPrec (sing @n) -> \case
        PUMinus bk a      -> PUMinus (f bk) (ePrecMorphism f g a)
        PNegate bk a      -> PNegate (f bk) (ePrecMorphism f g a)
        OfHigherPrefixPrec a -> OfHigherPrefixPrec (ePrecMorphism f g a)
      | Just Refl <- matches @8 (sing @n) -> \case
        PPower bk a b     -> PPower (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        OfHigher8 a -> OfHigher8 (ePrecMorphism f g a)
      | Just Refl <- matches @7 (sing @n) -> \case
        PMul bk a b       -> PMul (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PDiv bk a b       -> PDiv (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PMod bk a b       -> PMod (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        OfHigher7 a -> OfHigher7 (ePrecMorphism f g a)
      | Just Refl <- matches @6 (sing @n) -> \case
        PPlus bk a b      -> PPlus (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PMinus bk a b     -> PMinus (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PAppend bk a b    -> PAppend (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        OfHigher6 a-> OfHigher6 (ePrecMorphism f g a)
      | Just Refl <- matches @4 (sing @n) -> \case
        PEQ bk a b        -> PEQ (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PLT bk a b        -> PLT (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PLTEQ bk a b      -> PLTEQ (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PGTEQ bk a b      -> PGTEQ (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PGT bk a b        -> PGT (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PNEQ bk a b       -> PNEQ (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        OfHigher4 a -> OfHigher4 (ePrecMorphism f g a)
      | Just Refl <- matches @3 (sing @n) -> \case
        POr bk a b        -> POr (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        PAnd bk a b       -> PAnd (f bk) (ePrecMorphism f g a) (ePrecMorphism f g b)
        OfHigher3 a -> OfHigher3 (ePrecMorphism f g a)
      | Just Refl <- matches @1 (sing @n) -> \case
        PLambda bk args mt body -> PLambda (f bk)  (f' <$> args) mt (ePrecMorphism f g body)
          where
          f' (a,b) =  (ePrecMorphism f g a, b)
        OfHigher1 body -> OfHigher1 (ePrecMorphism f g body)
      | Just Refl <- matches @0 (sing @n) -> \case
        OfHigher0 body -> OfHigher0 (ePrecMorphism f g body)
      | otherwise -> error "EPrec can only be one of the following: Inf, PostfixPrec, PrefixPrec,8,7,6,5,4,3,2,1,0."



-- | Expression trees for attoms
data instance EPrec ctx Atom where
  -- | Integers @-1,2,3,-100,....@
  PInt     :: EIX ctx -> Int    -> EPrec ctx Atom
  -- | Floats @-1.0,2.0,3.14,-100.0,....@
  PFloat :: EFX ctx -> Double -> EPrec ctx Atom
  -- | Boolean values @True,False@
  PBool    :: EBX ctx -> Bool   -> EPrec ctx Atom
  -- | Strings @\"hello world\", \"lilly\", \"zilly\"@
  PString  :: ESX ctx -> String -> EPrec ctx Atom
  -- | Variables: any identifier
  PVar     :: EVX ctx  -> String -> EPrec ctx Atom
  -- | Tuples @(expr,expr)@
  PTuple   :: forall n ctx. (SingI n,(n < Atom) ~ True)
    => ETX ctx -> EPrec ctx n -> EPrec ctx n -> [EPrec ctx n] -> EPrec ctx Atom
  -- | parenthesis: @(expr)@
  PParen   :: forall n ctx. (SingI n,(n < Atom) ~ True)
    => EPX ctx -> EPrec ctx n    -> EPrec ctx Atom
  -- | Arrays: @[expr,expr,expr,...]@
  PArray :: forall n ctx. (SingI n,(n < Atom) ~ True)
    => EAX ctx -> [EPrec ctx n] -> EPrec ctx Atom
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
  PMatch
    :: EMatchX ctx
    -> EPrec ctx 0
    -> [(PPattern ctx, EPrec ctx 0)]
    -> EPrec ctx Atom
  PECons :: EECons ctx -> String -> [EPrec ctx 0] -> EPrec ctx Atom
  PEARecord :: EARecordX ctx -> [(String, EPrec ctx 0)] -> EPrec ctx Atom

type family EIX (ctx :: Type) :: Type
type family EFX (ctx :: Type) :: Type
type family EBX (ctx :: Type) :: Type
type family ESX (ctx :: Type) :: Type
type family EVX (ctx :: Type) :: Type
type family ETX (ctx :: Type) :: Type
type family EPX (ctx :: Type) :: Type
type family EDefX (ctx :: Type) :: Type
type family EIfX (ctx :: Type) :: Type
type family EAX (ctx :: Type) :: Type
type family EMatchX  (ctx :: Type) :: Type
type family EECons (ctx :: Type) :: Type
type family EARecordX (ctx :: Type) :: Type

type instance EIX ParsingStage = BookeepInfo
type instance EFX ParsingStage = BookeepInfo
type instance EBX ParsingStage = BookeepInfo
type instance ESX ParsingStage = BookeepInfo
type instance EVX ParsingStage = BookeepInfo
type instance ETX ParsingStage = BookeepInfo
type instance EPX ParsingStage = BookeepInfo
type instance EDefX ParsingStage = BookeepInfo
type instance EIfX ParsingStage = BookeepInfo
type instance EAX ParsingStage = BookeepInfo
type instance EMatchX  ParsingStage = BookeepInfo
type instance EECons ParsingStage = BookeepInfo
type instance EARecordX ParsingStage = BookeepInfo


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

mkFloat :: forall {n0}. (n0 ~ Atom)
  =>  Parser (Double -> EPrec ParsingStage n0)
mkFloat = PFloat <$> mkBookeepInfo

mkBool :: forall {n0}. (n0 ~ Atom)
  =>  Parser (Bool -> EPrec ParsingStage n0)
mkBool = PBool <$> mkBookeepInfo

mkString :: forall {n0}. (n0 ~ Atom)
  =>  Parser (String -> EPrec ParsingStage n0)
mkString = PString <$> mkBookeepInfo


mkVar :: forall {n0}. (n0 ~ Atom)
  =>  Parser (String -> EPrec ParsingStage n0)
mkVar = PVar <$> mkBookeepInfo

mkParen :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True)
  =>  Parser (EPrec ParsingStage n) -> Parser (EPrec ParsingStage n0)
mkParen p = parens $ PParen <$> mkBookeepInfo <*> p

mkArray :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True)
  =>  Parser ([EPrec ParsingStage n]) -> Parser (EPrec ParsingStage n0)
mkArray p = between "[" "]" $ PArray <$> mkBookeepInfo <*> p


mkParenOrTupleP :: forall {n0} n. (SingI n, n0 ~ Inf, (n < n0) ~ True)
  => Parser (EPrec ParsingStage n -> [EPrec ParsingStage n] -> EPrec ParsingStage n0)
mkParenOrTupleP = f <$> mkBookeepInfo
  where
    f :: BookeepInfo -> EPrec ParsingStage n -> [EPrec ParsingStage n] -> EPrec ParsingStage n0
    f bk a = \case
      (b:bs) -> PTuple bk a b bs
      [] -> PParen bk a

pParenOrTupleP :: Parser (EPrec ParsingStage Atom)
pParenOrTupleP
  = parens (mkParenOrTupleP <*> expr <*> option [] ("," *> sepBy expr ",") )

pArray :: Parser (EPrec ParsingStage Atom)
pArray = mkArray (expr `sepBy` ",")

pNumber :: Parser (EPrec ParsingStage Atom)
pNumber = pNumber' <* spaces
  where
  f x bk = case x of
    Left i  -> PInt bk i
    Right f -> PFloat bk f

  pNumber'
      -- = flip f <$> mkBookeepInfo <*> fractional3 @Double False
      = flip f <$> mkBookeepInfo <*> decimalFract @Int @Double

pConsName :: Parser String
pConsName = (:) <$> char '#' <*> ident



mkDefer :: forall {n0} n. (SingI n,n0 ~ Atom, (n < n0) ~ True)
  =>  Parser (EPrec ParsingStage n) -> Parser (EPrec ParsingStage n0)
mkDefer p = quoted $ PDefer <$> mkBookeepInfo <*> p


pDefer :: Parser (EPrec ParsingStage Atom)
pDefer = mkDefer expr

pIf :: Parser (EPrec ParsingStage Atom)
pIf = mkIf ((,,) <$> (expr <* ",")  <*> (expr <* ",") <*> expr)

pBool :: Parser (EPrec ParsingStage Atom)
pBool = mkBool <*> ("True" $> True <|> "False" $> False)

pString :: Parser (EPrec ParsingStage Atom)
pString = PString <$> mkBookeepInfo <*> (char '"' >> f)
  where
  f = do
    b <- Text.Parsec.many (noneOf ['"','\\'])
    c <- anyChar
    case c of
      '"' -> pure b
      '\\' -> do
        c' <- anyChar
        mappend (b <> ['\\',c']) <$> f
      _ -> error "pString is buggy."


mkMatch ::  Parser (EPrec ParsingStage Atom)
mkMatch = PMatch
  <$> (mkBookeepInfo <* "match")
  <*> (expr <* "with")
  <*> sepBy ((,) <$> pPPattern <*> ( "->" *> expr)) "|"


mkECons :: forall {n0}. (n0 ~ Atom)
  => Parser (String -> [EPrec ParsingStage 0] -> EPrec ParsingStage n0)
mkECons = PECons <$> mkBookeepInfo

mkEARecord :: forall {n0}. (n0 ~ Atom)
  => Parser (EPrec ParsingStage n0)
mkEARecord = PEARecord <$> mkBookeepInfo <*> between "{" "}" (field `sepBy` ",")
  where
    field :: Parser (String, EPrec ParsingStage 0)
    field = (,) <$> (ident <* ":=") <*> expr

atom :: Parser (EPrec ParsingStage Atom)
atom
  -- = pNumber
  -- <|> pString
  = pString
  <|> pDefer
  <|> pArray
  <|> pIf
  <|> pParenOrTupleP
  <|> pBool
  <|> mkMatch
  <|> mkEARecord
  <|> mkECons <*> pConsName <*> between "(" ")" (expr `sepBy` ",")
  <|> mkVar    <*> ident
  <|> pNumber


-----------------------------------
-- Precedence AppPrec Expressions
-----------------------------------

data instance EPrec ctx PrefixPrec where
  PUMinus :: EUMX ctx -> EPrec ctx PrefixPrec -> EPrec ctx PrefixPrec
  PNegate :: ENegateX ctx -> EPrec ctx PrefixPrec -> EPrec ctx PrefixPrec
  OfHigherPrefixPrec :: forall n ctx. (SingI n,(n > PrefixPrec) ~ True)
    => EPrec ctx n -> EPrec ctx PrefixPrec

type family EUMX (ctx :: Type) :: Type
type family ENegateX (ctx :: Type) :: Type
type instance EUMX ParsingStage = BookeepInfo
type instance ENegateX ParsingStage = BookeepInfo

mkUMinus :: Parser (EPrec ParsingStage PrefixPrec -> EPrec ParsingStage PrefixPrec)
mkUMinus = PUMinus <$> mkBookeepInfo

mkNegate :: Parser (EPrec ParsingStage PrefixPrec -> EPrec ParsingStage PrefixPrec)
mkNegate = PNegate <$> mkBookeepInfo

data instance EPrec ctx PostfixPrec where
  -- Function applications: @expr(expr00,expr01,....)(expr10,expr11,...)...@
  PApp    :: EAppX ctx -> EPrec ctx PostfixPrec -> [EPrec ctx 0] -> EPrec ctx PostfixPrec
  PAppArr :: EAAppX ctx -> EPrec ctx PostfixPrec -> [PIndexerExpression ctx] -> EPrec ctx PostfixPrec
  PDotApp :: EDAppX ctx -> EPrec ctx PostfixPrec -> String -> EPrec ctx PostfixPrec
  OfHigherPostfixPrec :: forall n ctx. (SingI n,(n > PostfixPrec) ~ True)
    => EPrec ctx n -> EPrec ctx PostfixPrec

type family EAppX (ctx :: Type)  :: Type
type family EAAppX (ctx :: Type) :: Type
type family EDAppX (ctx :: Type) :: Type

type instance EAppX ParsingStage = BookeepInfo
type instance EAAppX ParsingStage = BookeepInfo
type instance EDAppX ParsingStage = BookeepInfo

mkApp :: Parser (EPrec ParsingStage 0) -> Parser (EPrec ParsingStage PostfixPrec -> EPrec ParsingStage PostfixPrec)
mkApp p =  (\p' x y -> PApp p' y x ) <$> mkBookeepInfo <*> between "(" ")" (p `sepBy` ",")

mkAppArr :: Parser (PIndexerExpression ParsingStage) -> Parser (EPrec ParsingStage PostfixPrec -> EPrec ParsingStage PostfixPrec)
mkAppArr p =  (\p' x y -> PAppArr p' y x ) <$> mkBookeepInfo <*> between "[" "]" (p `sepBy` ",")

mkDotApp :: Parser (EPrec ParsingStage PostfixPrec -> EPrec ParsingStage PostfixPrec)
mkDotApp = (\p' x y -> PDotApp p' y x ) <$> mkBookeepInfo <*> (char '.' *> ident)

data PIndexerExpression ctx
  = PRangeIndexer (EPrec ctx 0, EPrec ctx 0)
  | PIndex (EPrec ctx 0)

foldPIndexerExpression :: (EPrec ctx 0 -> EPrec ctx 0 -> r) -> (EPrec ctx 0 -> r) -> PIndexerExpression ctx -> r
foldPIndexerExpression f g = \case
  PRangeIndexer (a,b) -> f a b
  PIndex a            -> g a

pIndexerExpression :: Parser (PIndexerExpression ParsingStage)
pIndexerExpression = f <$> eOrInt <*> optionMaybe (".." *> expr)
  where
    eOrInt :: Parser (EPrec ParsingStage 0)
    eOrInt = OfHigher0 <$> (mkInt <*> decimal <* spaces) <|> expr
    f :: EPrec ParsingStage 0 -> Maybe (EPrec ParsingStage 0) -> PIndexerExpression ParsingStage
    f a (Just b) = PRangeIndexer (a,b)
    f a Nothing  = PIndex a

------------------------------
-- Precedence 8 Expressions
------------------------------

-- | Precedence 8 operators.
data instance EPrec ctx 8 where
  -- | Power operator: @expr^expr@, right associative.
  PPower    :: forall n ctx. (SingI n,(n > 8) ~ True)
    => EPowX ctx -> EPrec ctx n -> EPrec ctx 8 -> EPrec ctx 8
  OfHigher8 :: forall n ctx. (SingI n,(n > 8) ~ True)
    =>EPrec ctx n                -> EPrec ctx 8

type family EPowX (ctx :: Type) :: Type
type instance EPowX ParsingStage = BookeepInfo

mkPower :: forall {n0} n. (SingI n,n0 ~ 8, (n > n0) ~ True)
  => Parser (EPrec ParsingStage n -> EPrec ParsingStage n0 -> EPrec ParsingStage n0)
mkPower = PPower <$> mkBookeepInfo

------------------------------
-- Precedence 7 Expressions
------------------------------

-- | Precedence 7 operators.
data instance EPrec ctx 7 where
  -- | Multiplication operator: @expr * expr@, left associative.
  PMul      :: forall n ctx. (SingI n,(n > 7) ~ True)
    => EMulX ctx-> EPrec ctx 7 -> EPrec ctx n -> EPrec ctx 7
  -- | Division operator: @expr / expr@, left associative.
  PDiv      :: forall n ctx. (SingI n,(n > 7) ~ True)
    => EDivX ctx -> EPrec ctx 7 -> EPrec ctx n -> EPrec ctx 7
  -- | Mod operator: @expr % expr@, left associative.
  PMod      :: forall n ctx. (SingI n,(n > 7) ~ True)
    => EModX ctx -> EPrec ctx 7 -> EPrec ctx n -> EPrec ctx 7
  OfHigher7 :: forall n ctx. (SingI n,(n > 7) ~ True)
    =>                           EPrec ctx n -> EPrec ctx 7

type family EMulX (ctx :: Type) :: Type
type family EDivX (ctx :: Type) :: Type
type family EModX (ctx :: Type) :: Type

type instance EMulX ParsingStage = BookeepInfo
type instance EDivX ParsingStage = BookeepInfo
type instance EModX ParsingStage = BookeepInfo

mkMul :: forall {n0} n. (SingI n,n0 ~ 7, (n > n0) ~ True) => Parser (EPrec ParsingStage n0 -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkMul = PMul <$> mkBookeepInfo

mkDiv :: forall {n0} n. (SingI n,n0 ~ 7, (n > n0) ~ True) => Parser (EPrec ParsingStage n0 -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkDiv = PDiv <$> mkBookeepInfo

mkMod :: forall {n0} n. (SingI n,n0 ~ 7, (n > n0) ~ True) => Parser (EPrec ParsingStage n0 -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkMod = PMod <$> mkBookeepInfo


------------------------------
-- Precedence 6 Expressions
------------------------------

-- | Precedence 6 operators.
data instance EPrec ctx 6 where
  -- | Plus operator: @expr + expr@, left associative.
  PPlus     :: forall n ctx. (SingI n,(n > 6) ~ True)
    => EPlusX ctx -> EPrec ctx 6 ->  EPrec ctx n -> EPrec ctx 6
  -- | Minus operator: @expr - expr@, left associative.
  PMinus    :: forall n ctx. (SingI n,(n > 6) ~ True)
    => EMinusX ctx -> EPrec ctx 6 ->  EPrec ctx n -> EPrec ctx 6
  PAppend  :: forall n ctx. (SingI n,(n > 6) ~ True)
    => EAppendX ctx -> EPrec ctx 6 ->  EPrec ctx n -> EPrec ctx 6
  OfHigher6 :: forall n ctx. (SingI n,(n > 6) ~ True)
    =>                            EPrec ctx n -> EPrec ctx 6

type family EPlusX (ctx :: Type) :: Type
type family EMinusX (ctx :: Type) :: Type
type family EAppendX (ctx :: Type) :: Type

type instance EPlusX ParsingStage  = BookeepInfo
type instance EMinusX ParsingStage = BookeepInfo
type instance EAppendX ParsingStage = BookeepInfo

mkMinus :: forall {n0} n . (SingI n,n0 ~ 6, (n > n0) ~ True) => Parser (EPrec ParsingStage n0 -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkMinus = PMinus <$> mkBookeepInfo

mkPlus :: forall {n0} n . (SingI n,n0 ~ 6, (n > n0) ~ True) => Parser (EPrec ParsingStage n0 -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPlus = PPlus <$> mkBookeepInfo

mkAppend :: forall {n0} n . (SingI n,n0 ~ 6, (n > n0) ~ True) => Parser (EPrec ParsingStage n0 -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkAppend = PAppend <$> mkBookeepInfo

------------------------------
-- Precedence 4 Expressions
------------------------------

-- | Precedence 4 operators.
data instance EPrec ctx 4 where
  -- | Less Than operator: @expr < expr@, non assoc associative.
  PLT       :: forall n ctx. (SingI n,(n > 4) ~ True)
    => EPLTX ctx -> EPrec ctx n ->  EPrec ctx n -> EPrec ctx 4
  -- | Less Than or Equal operator: @expr <= expr@, non assoc associative.
  PLTEQ     :: forall n ctx. (SingI n,(n > 4) ~ True)
    => EPLTEQX ctx -> EPrec ctx n ->  EPrec ctx n -> EPrec ctx 4
  -- | Greater Than operator: @expr > expr@, non assoc associative.
  PGT       :: forall n ctx. (SingI n,(n > 4) ~ True)
    => EPGTX ctx -> EPrec ctx n ->  EPrec ctx n -> EPrec ctx 4
  -- | Greater Than or Equal operator: @expr >= expr@, non assoc associative.
  PGTEQ     :: forall n ctx. (SingI n,(n > 4) ~ True)
    => EPGTEQX ctx -> EPrec ctx n ->  EPrec ctx n -> EPrec ctx 4
  -- | Equal operator: @expr = expr@, non assoc associative.
  PEQ       :: forall n ctx. (SingI n,(n > 4) ~ True)
    => EPEQX ctx -> EPrec ctx n ->  EPrec ctx n -> EPrec ctx 4
  -- | Different operator : @expr <> expr@, non assoc associative.
  PNEQ      :: forall n ctx. (SingI n,(n > 4) ~ True)
    => EPNEQX ctx -> EPrec ctx n ->  EPrec ctx n -> EPrec ctx 4
  OfHigher4 :: forall n ctx. (SingI n,(n > 4) ~ True)
    =>                            EPrec ctx n -> EPrec ctx 4

type family EPLTX   (ctx :: Type) :: Type
type family EPLTEQX (ctx :: Type) :: Type
type family EPGTX   (ctx :: Type) :: Type
type family EPGTEQX (ctx :: Type) :: Type
type family EPEQX   (ctx :: Type) :: Type
type family EPNEQX  (ctx :: Type) :: Type

type instance EPLTX   ParsingStage = BookeepInfo
type instance EPLTEQX ParsingStage = BookeepInfo
type instance EPGTX   ParsingStage = BookeepInfo
type instance EPGTEQX ParsingStage = BookeepInfo
type instance EPEQX   ParsingStage = BookeepInfo
type instance EPNEQX  ParsingStage = BookeepInfo


mkPLT :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPLT = PLT <$>  mkBookeepInfo

mkPLTEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPLTEQ = PLTEQ <$>  mkBookeepInfo

mkPGT :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPGT  = PGT <$>  mkBookeepInfo

mkPGTEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPGTEQ = PGTEQ <$>  mkBookeepInfo

mkPEQ :: forall {n0} n. (SingI n,n0 ~ 4, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPEQ  = PEQ <$>  mkBookeepInfo

mkPNEQ :: forall {n0} n. (SingI n,n0~ 4, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage n -> EPrec ParsingStage n0)
mkPNEQ = PNEQ <$>  mkBookeepInfo

------------------------------
-- Precedence 3 Expressions
------------------------------

-- | Precedence 3 operators.
data instance EPrec ctx 3 where
  PAnd    :: forall n ctx. (SingI n,(n > 3) ~ True)
    => EAndX ctx -> EPrec ctx n ->  EPrec ctx 3 -> EPrec ctx 3
  POr     :: forall n ctx. (SingI n,(n > 3) ~ True)
    => EOrX ctx -> EPrec ctx n ->  EPrec ctx 3 -> EPrec ctx 3
  OfHigher3 :: forall n ctx. (SingI n,(n > 3) ~ True)
    =>                            EPrec ctx n -> EPrec ctx 3

type family EAndX (ctx :: Type) :: Type
type family EOrX  (ctx :: Type) :: Type
type instance EAndX ParsingStage = BookeepInfo
type instance EOrX  ParsingStage = BookeepInfo

mkAnd :: forall {n0} n. (SingI n,n0 ~ 3, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage 3 -> EPrec ParsingStage n0)
mkAnd = PAnd <$> mkBookeepInfo

mkOr :: forall {n0} n. (SingI n,n0 ~ 3, (n > n0) ~ True) => Parser (EPrec ParsingStage n -> EPrec ParsingStage 3 -> EPrec ParsingStage n0)
mkOr = POr <$> mkBookeepInfo




------------------------------
-- Precedence 1 Expressions
------------------------------


data instance EPrec ctx 1 where
-- | Lambda functions:
  -- @
  --  fn(type0 var0, type1 var1,...) => return_type -> expr
  --  fn(type0 var0, type1 var1,...) -> expr
  -- @
  PLambda
    :: ELambdaX ctx
    -> [(EPrec ctx 0, T.Types)]
    -> Maybe T.Types
    -> EPrec ctx 1
    -> EPrec ctx 1
  OfHigher1 :: forall n ctx. (SingI n,(n > 1) ~ True) => EPrec ctx n -> EPrec ctx 1

type family ELambdaX (ctx :: Type) :: Type
type instance ELambdaX ParsingStage = BookeepInfo


mkLambda :: Parser (EPrec ParsingStage 1 -> EPrec ParsingStage 1)
mkLambda
  = (PLambda
  <$> (mkBookeepInfo <* "fn" )
  <*> parens (liftA2 (\t e -> (e,t2NT t)) pTypes expr `sepBy` ",")
  <*> optionMaybe ("=>" *> fmap t2NT pTypes) )
  <* "->"



----------------------------------
-- Pattern Matching Expressions
----------------------------------

type PatCtxMonoW ctx = PLVarCtx ctx

type PatCtxMono ctx =
  ( PLVarCtx ctx ~ PLWCCtx ctx
  , PLVarCtx ctx ~ PLIntCtx ctx
  , PLVarCtx ctx ~ PLBoolCtx ctx
  , PLVarCtx ctx ~ PLStringCtx ctx
  , PLVarCtx ctx ~ PLFloatCtx ctx
  , PLVarCtx ctx ~ PLTupleCtx ctx
  , PLVarCtx ctx ~ PLConsCtx ctx
  , PLVarCtx ctx ~ PLARecordCtx ctx
  , PLVarCtx ctx ~ ExprGuardCtx ctx
  , PLVarCtx ctx ~ BindingGuardCtx ctx
  )

patPrecMorphism :: forall f ctx ctx'.
  ( PatCtxMono ctx
  , PatCtxMono ctx'
  , ECtxMono ctx
  , ECtxMono ctx'
  )
  => (PatCtxMonoW ctx -> PatCtxMonoW ctx')
  -> (ECtxMonoW ctx -> ECtxMonoW ctx')
  -> PPattern ctx -> PPattern ctx'
patPrecMorphism f g (MkPPattern p gs) = MkPPattern
  (plPatPrecMorphism f g p)
  (patGuardPrecMorphism f g <$> gs)

plPatPrecMorphism :: forall f ctx ctx'.
  ( PatCtxMono ctx
  , PatCtxMono ctx'
  , ECtxMono ctx
  , ECtxMono ctx'
  )
  => (PatCtxMonoW ctx -> PatCtxMonoW ctx')
  -> (ECtxMonoW ctx -> ECtxMonoW ctx')
  -> PLPattern ctx -> PLPattern ctx'
plPatPrecMorphism f g = \case
  PLVarPattern bk name -> PLVarPattern (f bk) name
  PLWildcardPattern bk -> PLWildcardPattern (f bk)
  PLIntPattern bk i -> PLIntPattern (f bk) i
  PLBoolPattern bk b -> PLBoolPattern (f bk) b
  PLStringPattern bk s -> PLStringPattern (f bk) s
  PLFloatPattern bk d -> PLFloatPattern (f bk) d
  PLTuplePattern bk p1 p2 ps -> PLTuplePattern
    (f bk)
    (plPatPrecMorphism f g p1)
    (plPatPrecMorphism f g p2)
    (plPatPrecMorphism f g <$> ps)
  PLConstructorPattern bk name ps -> PLConstructorPattern
    (f bk)
    name
    (plPatPrecMorphism f g <$> ps)
  PLARecordPattern bk fields -> PLARecordPattern (f bk) fields



patGuardPrecMorphism :: forall f ctx ctx'.
  ( PatCtxMono ctx
  , PatCtxMono ctx'
  , ECtxMono ctx
  , ECtxMono ctx'
  )
  => (PatCtxMonoW ctx -> PatCtxMonoW ctx')
  -> (ECtxMonoW ctx -> ECtxMonoW ctx')
  -> PPaternGuard ctx -> PPaternGuard ctx'
patGuardPrecMorphism f g = \case
  PExprGuard bk expr -> PExprGuard (f bk) (ePrecMorphism g f  expr)
  PBindingGuard bk pat expr -> PBindingGuard (f bk) (plPatPrecMorphism f g pat) (ePrecMorphism g f expr)

data PPattern ctx
  = MkPPattern (PLPattern ctx) [PPaternGuard ctx]

pPPattern :: Parser (PPattern ParsingStage)
pPPattern = MkPPattern <$> pLPattern <*> option [] (between "<" ">" (pBindingGuard `sepBy` ","))


data PLPattern ctx where
  PLVarPattern :: PLVarCtx ctx -> String -> PLPattern ctx
  PLWildcardPattern :: PLWCCtx ctx -> PLPattern ctx
  PLIntPattern :: PLIntCtx ctx -> Int -> PLPattern ctx
  PLBoolPattern :: PLBoolCtx ctx -> Bool -> PLPattern ctx
  PLStringPattern :: PLStringCtx ctx -> String -> PLPattern ctx
  PLFloatPattern :: PLFloatCtx ctx -> Double -> PLPattern ctx
  PLTuplePattern :: PLTupleCtx ctx -> PLPattern ctx -> PLPattern ctx -> [PLPattern ctx] -> PLPattern ctx
  PLConstructorPattern :: PLConsCtx ctx -> String -> [PLPattern ctx] -> PLPattern ctx
  PLARecordPattern :: PLARecordCtx ctx -> [(String, T.Types)] -> PLPattern ctx

type family PLVarCtx     (ctx :: Type) :: Type
type family PLWCCtx      (ctx :: Type) :: Type
type family PLIntCtx     (ctx :: Type) :: Type
type family PLBoolCtx    (ctx :: Type) :: Type
type family PLStringCtx  (ctx :: Type) :: Type
type family PLFloatCtx   (ctx :: Type) :: Type
type family PLTupleCtx   (ctx :: Type) :: Type
type family PLConsCtx    (ctx :: Type) :: Type
type family PLARecordCtx (ctx :: Type) :: Type

type instance PLVarCtx     ParsingStage = BookeepInfo
type instance PLWCCtx      ParsingStage = BookeepInfo
type instance PLIntCtx     ParsingStage = BookeepInfo
type instance PLBoolCtx    ParsingStage = BookeepInfo
type instance PLStringCtx  ParsingStage = BookeepInfo
type instance PLFloatCtx   ParsingStage = BookeepInfo
type instance PLTupleCtx   ParsingStage = BookeepInfo
type instance PLConsCtx    ParsingStage = BookeepInfo
type instance PLARecordCtx ParsingStage = BookeepInfo


pLVarPattern :: Parser (PLPattern ParsingStage)
pLVarPattern = PLVarPattern <$> mkBookeepInfo <*> ident

pLWildcardPattern :: Parser (PLPattern ParsingStage)
pLWildcardPattern = PLWildcardPattern <$> mkBookeepInfo <* (char '_' <* space <* spaces)

pLIntOrFloatPattern :: Parser (PLPattern ParsingStage)
pLIntOrFloatPattern = f <$> mkBookeepInfo <*> (floating3 @Double False <* spaces)
  where
    f :: BookeepInfo -> Double -> PLPattern ParsingStage
    f bk x = case x == fromInteger (round x) of
      True  -> PLIntPattern bk (round x)
      False -> PLFloatPattern bk x

pLBoolPattern :: Parser (PLPattern ParsingStage)
pLBoolPattern = PLBoolPattern <$> mkBookeepInfo <*> ("true" $> True <|> "false" $> False)

pLStringPattern :: Parser (PLPattern ParsingStage)
pLStringPattern = PLStringPattern <$> mkBookeepInfo <*> (char '"' >> f)
  where
  f = do
    b <- Text.Parsec.many (noneOf ['"','\\'])
    c <- anyChar
    case c of
      '"' -> pure b
      '\\' -> do
        c' <- anyChar
        mappend (b <> ['\\',c']) <$> f
      _ -> error "pLStringPattern is buggy."

pLTuplePattern :: Parser (PLPattern ParsingStage)
pLTuplePattern
  = PLTuplePattern
  <$> mkBookeepInfo
  <*> ("(" *>  pLPattern)
  <*> ("," *> pLPattern)
  <*> option [] ("," *> sepBy pLPattern",")
  <* ")"

pLConstructorPattern :: Parser (PLPattern ParsingStage)
pLConstructorPattern
  = PLConstructorPattern
  <$> mkBookeepInfo
  <*> pConsName
  <*> Text.Parsec.many pLPattern

pLARecordPattern :: Parser (PLPattern ParsingStage)
pLARecordPattern
  = PLARecordPattern
  <$> mkBookeepInfo
  <*> between "{" "}" (fieldPattern `sepBy` ",")
  where
    fieldPattern :: Parser (String, T.Types)
    fieldPattern = (,) <$> (ident <* ":") <*> (t2NT <$> pTypes)


pLPattern :: Parser (PLPattern ParsingStage)
pLPattern
  = try pLWildcardPattern
  <|> pLIntOrFloatPattern
  <|> pLBoolPattern
  <|> pLStringPattern
  <|> pLTuplePattern
  <|> pLConstructorPattern
  <|> pLARecordPattern
  <|> pLVarPattern

data PPaternGuard ctx where
  PExprGuard    :: ExprGuardCtx ctx -> EPrec ctx 0 -> PPaternGuard ctx
  PBindingGuard :: BindingGuardCtx ctx -> PLPattern ctx -> EPrec ctx 0 -> PPaternGuard ctx

type family ExprGuardCtx    (ctx :: Type) :: Type
type family BindingGuardCtx (ctx :: Type) :: Type

type instance ExprGuardCtx    ParsingStage = BookeepInfo
type instance BindingGuardCtx ParsingStage = BookeepInfo


pBindingGuard :: Parser (PPaternGuard ParsingStage)
pBindingGuard = PBindingGuard <$> mkBookeepInfo <*> pLPattern <*> ("<-" *> expr)

pPPatternGuard :: Parser (PPaternGuard ParsingStage)
pPPatternGuard = try pBindingGuard <|> (PExprGuard <$> mkBookeepInfo <*> expr)

------------------------------
-- Precedence 0 Expressions
------------------------------



-- | Expressions.
data instance EPrec ctx 0 where
  OfHigher0 :: forall n ctx. (SingI n, (n > 0) ~ True) => EPrec ctx n -> EPrec ctx 0

expr :: Parser (EPrec ParsingStage 0)
expr = fmap OfHigher0 . precedence $
  sops Prefix [mkLambda] |-<
  sops InfixR [ mkAnd <* "&&", mkOr <* "||"] |-<
  sops InfixN
    [ mkPLTEQ <* "<="
    , mkPGTEQ <* ">="
    , mkPNEQ  <* "<>"
    , mkPLT   <* "<"
    , mkPGT   <* ">"
    , mkPEQ   <* "="

    ] |-<
  sops InfixL
    [ mkMinus <* "-"
    , mkAppend <* "++"
    , mkPlus  <* "+"
    ] |-<
  sops InfixL
    [ mkMul <* "*"
    , mkDiv <* "/"
    , mkMod <* "%"
    ] |-<
  sops InfixR  [ mkPower  <* "^"] |-<
  sops Prefix  [ mkUMinus <* "-", mkNegate <* "~"] |-<
  sops Postfix
    [ mkApp    expr
    , mkAppArr pIndexerExpression
    , mkDotApp
    ] |-<

  Atom atom

instance (SingI n', SingI n, (n' > n) ~ True) => EPrec ctx n' PU.< EPrec ctx n where
  upcast = case () of
    _ | Just Refl <- matches @0 (sing @n) -> OfHigher0
    _ | Just Refl <- matches @1 (sing @n) -> OfHigher1
    _ | Just Refl <- matches @3 (sing @n) -> OfHigher3
    _ | Just Refl <- matches @4 (sing @n) -> OfHigher4
    _ | Just Refl <- matches @6 (sing @n) -> OfHigher6
    _ | Just Refl <- matches @7 (sing @n) -> OfHigher7
    _ | Just Refl <- matches @8 (sing @n) -> OfHigher8
    _ | Just Refl <- matches @PostfixPrec (sing @n) -> OfHigherPostfixPrec
    _ | Just Refl <- matches @PrefixPrec (sing @n) -> OfHigherPrefixPrec
    _ -> error "Error. Upcast Expression Precedences must be one of: 0,1,3,4,6,7,8,Postfix,Prefix."
  downcast t
    = withKnownNat (sing @n')
    $ withKnownNat (sing @n)
    $ case () of
      _ | Just Refl <- matches @0 (sing @n) -> case t of
        OfHigher0 f -> genericDowncast f
      _ | Just Refl <- matches @1 (sing @n) -> case t of
        OfHigher1 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @3 (sing @n) -> case t of
        OfHigher3 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @4 (sing @n) -> case t of
        OfHigher4 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @6 (sing @n) -> case t of
        OfHigher6 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @7 (sing @n) -> case t of
        OfHigher7 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @8 (sing @n) -> case t of
        OfHigher8 f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @PostfixPrec (sing @n) -> case t of
        OfHigherPostfixPrec f -> genericDowncast f
        _           -> Nothing
      _ | Just Refl <- matches @PrefixPrec (sing @n) -> case t of
        OfHigherPrefixPrec f -> genericDowncast f
        _           -> Nothing
      _ -> error "Error. Downcast Expression Precedences must be one of: 0,1,3,4,6,7,8,Postfix,Prefix."
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

type ACtxMonoW ctx = ADeclX ctx

type ACtxMono ctx =
  ( ADeclX ctx ~ AAssignX ctx
  , ADeclX ctx ~ APrintX ctx
  , ADeclX ctx ~ ATDeclX ctx
  , ADeclX ctx ~ SysCommandX ctx
  , ADeclX ctx ~ ASeqX ctx
  )

aPrecMorphism :: forall ctx ctx'.
  ( ACtxMono ctx
  , ACtxMono ctx'
  , ECtxMono ctx
  , ECtxMono ctx'
  , PatCtxMono ctx
  , PatCtxMono ctx'
  )
  => (ACtxMonoW ctx -> ACtxMonoW ctx')
  -> (ECtxMonoW ctx -> ECtxMonoW ctx')
  -> (PatCtxMonoW ctx -> PatCtxMonoW ctx')
  -> A1 ctx -> A1 ctx'
aPrecMorphism f g h = \case
  Seq x y ys -> Seq (f x) (a0PrecMorphism f g h y) (a0PrecMorphism f g h <$> ys)
  OfA0 y     -> OfA0 (a0PrecMorphism f g h y)

a0PrecMorphism :: forall ctx ctx'.
  ( ACtxMono ctx
  , ACtxMono ctx'
  , ECtxMono ctx
  , ECtxMono ctx'
  , PatCtxMono ctx
  , PatCtxMono ctx'
  )
  => (ACtxMonoW ctx -> ACtxMonoW ctx')
  -> (ECtxMonoW ctx -> ECtxMonoW ctx')
  -> (PatCtxMonoW ctx -> PatCtxMonoW ctx')
  -> A0 ctx -> A0 ctx'
a0PrecMorphism f g h = \case
  Decl t e1 e2 x      -> Decl t (ePrecMorphism g h e1) (ePrecMorphism g h e2) (f x)
  Assign e1 e2 x      -> Assign (ePrecMorphism g h e1) (ePrecMorphism g h e2) (f x)
  Print e x           -> Print (ePrecMorphism g h e) (f x)
  PTypeDef name cs x  -> PTypeDef name cs (f x)
  SysCommand name x   -> SysCommand name (f x)

data A1 ctx
  = Seq (ASeqX ctx) (A0 ctx) [A0 ctx]
  | OfA0 (A0 ctx)

type family ASeqX (ctx :: Type) :: Type

type instance ASeqX ParsingStage = BookeepInfo

pattern MkSeq :: A0 ctx -> [A0 ctx] -> A1 ctx
pattern MkSeq b bs <-  Seq _ b bs
  where MkSeq b bs = Seq undefined b bs

newtype Record = MkRecord { unRecord :: [(String,T.Types)]}

pProductTypeBody :: Parser [(BookeepInfo, T.Types)]
pProductTypeBody = (fmap . fmap) t2NT <$> Text.Parsec.many ((,) <$> mkBookeepInfo <*> pTypes)

data ProductConstructor = MkProductConstructor
  { pcName :: String
  , pcTypes :: [(BookeepInfo, T.Types)]
  }

pProductTypeCons :: Parser ProductConstructor
pProductTypeCons = MkProductConstructor
  <$> ( (:) <$> char '#' <*> ident )
  <*> pProductTypeBody

pSOP :: Parser [(BookeepInfo, ProductConstructor)]
pSOP = flip sepBy "|" $ (,) <$> mkBookeepInfo <*> pProductTypeCons


data A0 ctx
  = Decl T.Types (Expr ctx) (Expr ctx) (ADeclX ctx)
  | Assign (Expr ctx) (Expr ctx)     (AAssignX ctx)
  | Print (Expr ctx)           (APrintX ctx)
  | PTypeDef String [(BookeepInfo, ProductConstructor)] (ATDeclX ctx)
  | SysCommand String (SysCommandX ctx)

type family ADeclX      (ctx :: Type) :: Type
type family AAssignX    (ctx :: Type) :: Type
type family APrintX     (ctx :: Type) :: Type
type family ATDeclX     (ctx :: Type) :: Type
type family SysCommandX (ctx :: Type) :: Type

type instance ADeclX      ParsingStage  = BookeepInfo
type instance AAssignX    ParsingStage  = BookeepInfo
type instance APrintX     ParsingStage  = BookeepInfo
type instance SysCommandX ParsingStage  = BookeepInfo
type instance ATDeclX     ParsingStage  = BookeepInfo

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

mkTypeDef :: Parser (A0 ParsingStage)
mkTypeDef = mkBookeepInfo <**>
  (PTypeDef <$> ("type" *> ident) <*> (f <$> optionMaybe ( ":=" *> pSOP)))
  where f :: Maybe [(BookeepInfo, ProductConstructor)] -> [(BookeepInfo, ProductConstructor)]
        f (Just x) = x
        f Nothing  = []

a0 :: Parser (A0 ParsingStage)
a0
  =   mkSysCommand
  <|> mkTypeDef
  <|> flip Print <$> mkBookeepInfo <*> try (fully expr)
  <|> try (mkAssign expr expr)
  <|> (mkDecl (t2NT <$> pTypes) expr expr)

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


yieldArrAssign :: forall n ctx. SingI n => EPrec ctx n -> Maybe (String, [[PIndexerExpression ctx]])
yieldArrAssign x | Just Refl <- matches @0 (sing @n) = case x of
  OfHigher0 x' -> yieldArrAssign x'
yieldArrAssign x | Just Refl <- matches @1 (sing @n) = case x of
  OfHigher1 x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @3 (sing @n) = case x of
  OfHigher3 x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @4 (sing @n) = case x of
  OfHigher4 x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @6 (sing @n) = case x of
  OfHigher6 x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @7 (sing @n) = case x of
  OfHigher7 x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @8 (sing @n) = case x of
  OfHigher8 x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @PostfixPrec (sing @n) = case x of
  OfHigherPostfixPrec x' -> yieldArrAssign x'
  PAppArr _ e xs -> fmap (<> [xs]) <$> yieldArrAssign e
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @PrefixPrec (sing @n) = case x of
  OfHigherPrefixPrec x' -> yieldArrAssign x'
  _ -> Nothing
yieldArrAssign x | Just Refl <- matches @Atom (sing @n) = case x of
  PVar _ s -> Just (s, [])
  _        -> Nothing
yieldArrAssign _ = error "Error. yieldArrAssign Expression Precedences must be one of: 0,1,4,6,7,8,Postfix,Prefix."

yieldVarName :: forall n ctx. SingI n => EPrec ctx n -> Maybe String
yieldVarName x | Just Refl <- matches @0 (sing @n) = case x of
  OfHigher0 x' -> yieldVarName x'
yieldVarName x | Just Refl <- matches @1 (sing @n) = case x of
  OfHigher1 x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @3 (sing @n) = case x of
  OfHigher3 x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @4 (sing @n) = case x of
  OfHigher4 x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @6 (sing @n) = case x of
  OfHigher6 x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @7 (sing @n) = case x of
  OfHigher7 x' -> yieldVarName x'
  _ -> Nothing
yieldVarName x | Just Refl <- matches @8 (sing @n) = case x of
  OfHigher8 x' -> yieldVarName x'
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
yieldVarName _ = error "Error. yieldVar Expression Precedences must be one of: 0,1,4,6,7,8,Postfix,Prefix."

instance SingI n => Show (TPrec ctx n) where
  showsPrec p  = withKnownNat (sing @n) $ case (sameNat (sing @n) (SNat @Atom), sameNat (sing @n) (SNat @0)) of
    (Just Refl,_) -> \case
      TNormal _ "Tuple" (a:as)
        -> showString "("
        . foldl (\acc x -> acc . showString ", " . shows x) (shows a) as
        . showString ")"
      TNormal _ a []
        -> showString a
      TNormal _ a (b:bs)
        -> showString a
        . showString "<"
        . foldl (\acc x -> acc . showString ", " . shows x) (shows b ) bs
        . showString ">"
      TARecord _ (f : fields)
        -> showString "{"
        . foldl (\acc (n,t) -> acc . showString ", " . showString n . showString ": " . shows t) (showString (fst f) . showString ": " . shows (snd f)) fields
        . showString "}"
      TARecord _ []
        -> showString "{}"
      OfLowerTPrec a -> showString "(" . shows a . showString ")"
    (_, Just Refl) -> \case
      OfHigherTPrec0 a -> shows a
      TArrow _ a b -> showParen (p > 0) $ shows a . showString " => " . shows b
    _ -> const $ showString "Precedence not defined"


instance Show (PLPattern ctx) where
  show (PLVarPattern _ s) = s
  show (PLWildcardPattern _) = "_"
  show (PLIntPattern _ i) = show i
  show (PLBoolPattern _ b) = if b then "true" else "false"
  show (PLStringPattern _ s) = show s
  show (PLFloatPattern _ f) = show f
  show (PLTuplePattern _ p1 p2 ps) = "(" ++ intercalate ", " (map show (p1:p2:ps)) ++ ")"
  show (PLConstructorPattern _ name ps) = name ++ concatMap ((" " ++) . show) ps
  show (PLARecordPattern _ fields) = "{" ++ intercalate ", " (map (\(n,t) -> n ++ ": " ++ show t) fields) ++ "}"

instance Show (PPaternGuard ctx) where
  show (PExprGuard _ e) = show e
  show (PBindingGuard _ p e) = show p ++ " <- " ++ show e

instance Show (PPattern ctx) where
  show (MkPPattern p gs) = show p ++ case gs of
    [] -> ""
    _  -> "<" ++ intercalate ", " (map show gs) ++ ">"


instance SingI n => Show (EPrec ctx n) where

  showsPrec p = withKnownNat (sing @n) $ case () of
      () | Just Refl <- matches @0 (sing @n) -> \case
        OfHigher0 e -> showsPrec p e
      () | Just Refl <- matches @1 (sing @n) -> \case
        PLambda _ [(x,t)] mt e -> showParen (p > 1)
          $ showString "fn(" . shows t . showString " "
          . shows x . (maybe (showString "") $ \s -> showString " => " . shows s) mt
          . showString ") -> "
          . shows e
        PLambda ctx ((x,t) : xs) mt e -> showParen (p > 1)
          $ showString "fn(" . shows t . showString " "
          . shows x . (maybe (showString "") $ \s -> showString " => " . shows s) mt
          . showString ") -> "
          . showsPrec 1 (PLambda ctx xs mt e)
        PLambda _ [] _ e -> showParen (p > 1) $ showString "fn() -> " . shows e
        OfHigher1 x -> showsPrec p x
      () | Just Refl <- matches @3 (sing @n) -> \case
        PAnd _ a b -> showParen (p > 3) $ showsPrec 3 a . showString " && " . showsPrec 4 b
        POr _ a b -> showParen (p > 3) $ showsPrec 3 a . showString " || " . showsPrec 4 b
        OfHigher3 a -> showsPrec p a
      () | Just Refl <- matches @4 (sing @n) -> \case
        PLT _ a b -> showParen (p > 4) $ showsPrec 4 a . showString " < " . showsPrec 5 b
        PLTEQ _ a b -> showParen (p > 4) $ showsPrec 4 a . showString " <= " . showsPrec 5 b
        PGT _ a b -> showParen (p > 4) $ showsPrec 4 a . showString " > " . showsPrec 5 b
        PGTEQ _ a b -> showParen (p > 4) $ showsPrec 4 a . showString " >= " . showsPrec 5 b
        PEQ _ a b -> showParen (p > 4) $ showsPrec 4 a . showString " = " . showsPrec 5 b
        PNEQ _ a b -> showParen (p > 4) $ showsPrec 4 a . showString " <> " . showsPrec 5 b
        OfHigher4 a  -> showsPrec p a
      () | Just Refl <- matches @6 (sing @n) -> \case
        PPlus _ a b -> showParen (p > 6) $ showsPrec 6 a . showString " + " . showsPrec 7 b
        PMinus _ a b -> showParen (p > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
        PAppend _ a b -> showParen (p > 6) $ showsPrec 6 a . showString " ++ " . showsPrec 7 b
        OfHigher6 a  -> showsPrec p a
      () | Just Refl <- matches @7 (sing @n) -> \case
        PMul _ a b -> showParen (p > 7) $ showsPrec 7 a . showString " * " . showsPrec 8 b
        PDiv _ a b -> showParen (p > 7) $ showsPrec 7 a . showString " / " . showsPrec 8 b
        PMod _ a b -> showParen (p > 7) $ showsPrec 7 a . showString " % " . showsPrec 8 b
        OfHigher7 a -> showsPrec p a
      () | Just Refl <- matches @8 (sing @n) -> \case
        PPower _ a b -> showParen (p > 8) $ showsPrec 9 a . showString "^" . showsPrec 8 b
        OfHigher8 a -> showsPrec p a
      () | Just Refl <- matches @PrefixPrec (sing @n) -> \case
        PUMinus _ e -> showParen (p > 10) $ showString "-" . shows e
        PNegate _ e -> showParen (p > 10) $ showString "~" . shows e
        OfHigherPrefixPrec e -> showsPrec p e
      () | Just Refl <- matches @PostfixPrec (sing @n) -> \case
        PApp _ f (x:xs) -> showParen (p > 10)
          $ showsPrec 11 f
          . showParen True (foldr (\arg acc -> shows arg . showString ", " . acc) (shows x) xs)
        PAppArr _ f (x:xs) -> showParen (p > 10)
          $ showsPrec 11 f
          . showString "["
          . (foldr (\arg acc -> shows arg . showString ", " . acc) (shows x) xs)
          . showString "]"
        PApp _ f [] -> showParen (p > 10) $ showsPrec 11 f
        PAppArr _ f [] -> showParen (p > 10) $ showsPrec 11 f
        PDotApp _ e field -> showsPrec 11 e . showString "." . showString field
        OfHigherPostfixPrec a  -> showsPrec p a
      () | Just Refl <- matches @Atom (sing @n) -> \case
        PInt _ n -> shows n
        PVar _ n -> showString n
        PTuple _ a b bs
          -> showString "("
          . foldl (\acc x -> acc . showString ", " . shows x) (shows a) (b:bs)
          . showString ")"
        PFloat _ n -> shows n
        PBool _ b -> showString $ if b then "True" else "False"
        PString _ s -> showString "\"" . shows s . showString "\""
        PParen _ a -> showParen True $ shows a
        PDefer _ a -> showString "\"" . shows a . showString "\""
        PIf _ (a, b, c)
          -> showString "if(" . shows a . showString ", " . shows b
          . showString ", " . shows c . showString ")"
        PArray _ (x:xs)
          -> showString "["
          . foldr (\x acc -> shows x . showString ", " . acc) (shows x) xs
          . showString "]"
        PArray _ [] -> showString "[]"
        PMatch _ e (b : branches)
          -> showString "match " . shows e . showString " with\n "
          . foldl (\acc (p,g) -> acc . showString "| " . showString (show p) . showString " -> " . shows g . showString "\n ") (showString "| " . showString (show (fst b)) . showString " -> " . shows (snd b) . showString "\n ") branches
        PMatch _ e []
          -> showString "match " . shows e . showString " with\n "
          . showString "| _ -> ⊥ \n"
        PECons _ h t -> shows h . showString "( " . showString (intercalate "," $ show <$> t) . showString ")"
        PEARecord _ fields
          -> showString "{"
          . showString (intercalate ", " $ fmap (\(n,v) -> n ++ " := " ++ show v) fields)
          . showString "}"
      _ -> const $ showString "Precedence not defined"

instance Show (PIndexerExpression ctx) where
  show (PIndex e) = show e
  show (PRangeIndexer (e,e')) = show e <> " .. " <> show e'

instance Show ProductConstructor where
  show (MkProductConstructor n ts) = n <> concatMap (\(_,t) -> " " <> show t) ts

instance Show (A0 ctx) where
  show (Decl t e e' _) = show t <> " " <> show e <> " := " <> show e' <> ";"
  show (Assign e e' _) = show e <> " := " <> show e' <> ";"
  show (Print e _)     = show e
  show (SysCommand e _) = "sys." <> e <> "();"
  show (PTypeDef n cons _) = case fmap snd cons of
    [] -> "type " <> n <> ";"
    cons'  -> "type " <> n <> " := " <> intercalate " | " (show <$> cons') <> ";"

instance Show (A1 ctx) where
  show (OfA0 x) = show x
  show (Seq _ x xs) = unlines $ show x : fmap show xs

class HasBookeepInfo a where
  getBookeepInfo :: a -> BookeepInfo

instance HasBookeepInfo BookeepInfo where
  getBookeepInfo = id

instance SingI n => HasBookeepInfo (EPrec ParsingStage n) where
  getBookeepInfo = case () of
    _ | Just Refl <- matches @0 (sing @n) -> \case
      OfHigher0 x -> getBookeepInfo x
    _ | Just Refl <- matches @1 (sing @n) -> \case
      PLambda bk _ _ _  -> bk
      OfHigher1 x -> getBookeepInfo x
    _ | Just Refl <- matches @3 (sing @n) -> \case
      PAnd bk _ _ -> bk
      POr  bk _ _ -> bk
      OfHigher3 x -> getBookeepInfo x
    _ | Just Refl <- matches @4 (sing @n) -> \case
      PLT    bk _ _ -> bk
      PLTEQ  bk _ _ -> bk
      PGT    bk _ _ -> bk
      PGTEQ  bk _ _ -> bk
      PEQ    bk _ _ -> bk
      PNEQ   bk _ _ -> bk
      OfHigher4 x -> getBookeepInfo x
    _ | Just Refl <- matches @6 (sing @n) -> \case
      PPlus  bk _ _ -> bk
      PMinus bk _ _ -> bk
      PAppend bk _ _ -> bk
      OfHigher6 x -> getBookeepInfo x
    _ | Just Refl <- matches @7 (sing @n) -> \case
      PMul  bk _ _ -> bk
      PDiv  bk _ _ -> bk
      PMod  bk _ _ -> bk
      OfHigher7 x -> getBookeepInfo x
    _ | Just Refl <- matches @8 (sing @n) -> \case
      PPower bk _ _ -> bk
      OfHigher8 x -> getBookeepInfo x
    _ | Just Refl <- matches @PostfixPrec (sing @n) -> \case
      PApp    bk _ _ -> bk
      PAppArr bk _ _ -> bk
      PDotApp bk _ _ -> bk
      OfHigherPostfixPrec x -> getBookeepInfo x
    _ | Just Refl <- matches @PrefixPrec (sing @n) -> \case
      PUMinus bk _ -> bk
      PNegate bk _ -> bk
      OfHigherPrefixPrec x -> getBookeepInfo x
    _ | Just Refl <- matches @Atom (sing @n) -> \case
      PInt bk _ -> bk
      PVar bk _ -> bk
      PTuple bk _ _ _ -> bk
      PFloat bk _ -> bk
      PBool bk _ -> bk
      PString bk _ -> bk
      PParen bk _ -> bk
      PDefer bk _ -> bk
      PIf bk _ -> bk
      PMatch bk _ _ -> bk
      PArray bk _ -> bk
      PECons bk _ _ -> bk
      PEARecord bk _ -> bk
    _ -> error "Error. BookeepInfo not defined for this precedence."

genCtxInstances :: Name -> Name -> Q [Dec]
genCtxInstances ctxName tname = do
  t <- TH.conT tname
  ctx <- TH.conT ctxName
  let f x = TySynInstD
          $ TH.TySynEqn Nothing (TH.AppT (TH.ConT x) ctx) t

  let insts =
            [ ''EIX
            , ''EFX
            , ''EBX
            , ''ESX
            , ''EVX
            , ''ETX
            , ''EPX
            , ''EAX
            , ''EDefX
            , ''EIfX
            , ''EMatchX
            , ''EECons
            , ''EARecordX
            , ''EUMX
            , ''ENegateX
            , ''EAppX
            , ''EAAppX
            , ''EDAppX
            , ''EPowX
            , ''EMulX
            , ''EDivX
            , ''EModX
            , ''EPlusX
            , ''EMinusX
            , ''EAppendX
            , ''EPLTX
            , ''EPLTEQX
            , ''EPGTX
            , ''EPGTEQX
            , ''EPEQX
            , ''EPNEQX
            , ''EAndX
            , ''EOrX
            , ''ELambdaX
            , ''PLVarCtx
            , ''PLWCCtx
            , ''PLIntCtx
            , ''PLBoolCtx
            , ''PLStringCtx
            , ''PLFloatCtx
            , ''PLTupleCtx
            , ''PLConsCtx
            , ''PLARecordCtx
            , ''ExprGuardCtx
            , ''BindingGuardCtx
            , ''ASeqX
            , ''ADeclX
            , ''AAssignX
            , ''APrintX
            , ''ATDeclX
            , ''SysCommandX

            ]

  pure $ f <$> insts
