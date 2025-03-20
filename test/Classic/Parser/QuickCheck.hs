{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE PackageImports             #-}
module Classic.Parser.QuickCheck where

import Debug.Trace (trace)
import Parser.Classic.ZillyParser
import Test.Framework.QuickCheckWrapper
import Text.Parsec.Pos
import Data.Coerce (coerce)
import Control.Monad



--------------------------
-- Parser Generators
--------------------------

newtype ExprGen = ExprGen Expr deriving newtype Show
newtype TermGen = TermGen Term deriving newtype Show
newtype AtomGen = AtomGen Atom deriving newtype Show

newtype TypesGen = TypesGen Types deriving newtype Show
newtype Types0Gen = Types0Gen Types0 deriving newtype Show

newtype A0Gen = A0Gen A0 deriving newtype Show
newtype A1Gen = A1Gen A1 deriving newtype Show


--------------------------
-- Sizes
--------------------------

maxDepth :: Int
maxDepth = 5

maxIdentLength :: Int
maxIdentLength = 15

withMaxLength :: Int -> (Int -> a) -> (Int -> a)
withMaxLength l f = \n -> f (min n l)


--------------------------
-- Smart constructors
--------------------------


mkMinus :: Gen (Expr -> Term -> Expr)
mkMinus = (\p x y -> Minus x y p) <$> arbitrarySourcePos

mkLess :: Gen (Expr -> Term -> Expr)
mkLess = (\p x y -> Minus x y p) <$> arbitrarySourcePos

mkOfTerm :: Gen (Term -> Expr)
mkOfTerm = pure OfTerm

mkApp :: Gen (Term -> Expr -> Term)
mkApp = do
  f <- (\p x y -> App x y p) <$> arbitrarySourcePos
  g <- mkParens 
  pure . flip $ flip f . (OfTerm . OfAtom) . g  

mkOfAtom :: Gen (Atom -> Term)
mkOfAtom = pure OfAtom

mkVal :: Gen (Int-> Atom)
mkVal = flip Val <$> arbitrarySourcePos

mkVar :: Gen (IdentifierGen -> Atom)
mkVar = (\p x -> Var (coerce x) p) <$> arbitrarySourcePos

mkParens :: Gen (Expr -> Atom)
mkParens = (\p x -> Parens x p) <$> arbitrarySourcePos

mkDefer :: Gen (Expr -> Atom)
mkDefer = (\p x -> Defer x p) <$> arbitrarySourcePos

mkFormula :: Gen (Expr -> Atom)
mkFormula = do 
  f <- (\p x -> Formula x p) <$> arbitrarySourcePos
  g <- mkParens 
  pure $ f . (OfTerm . OfAtom) . g 


mkIfThenElse :: Gen (Expr -> Expr -> Expr -> Atom)
mkIfThenElse = (\p x y z -> IfThenElse x y z p) <$> arbitrarySourcePos

mkLambda :: Gen (IdentifierGen -> Types -> Expr -> Atom)
mkLambda = (\p x y z -> Lambda (coerce x) y z p) <$> arbitrarySourcePos

mkZ :: Gen Types0
mkZ = Z <$> arbitrarySourcePos

mkLazy :: Gen (Types -> Types0)
mkLazy = (\p x -> Lazy x p) <$> arbitrarySourcePos

mkLazyS :: Gen (Types -> Types0)
mkLazyS = (\p x -> LazyS x p) <$> arbitrarySourcePos

mkTParen :: Gen (Types -> Types0)
mkTParen = (\p x -> TParen x p) <$> arbitrarySourcePos

mkArrow :: Gen (Types0 -> Types -> Types)
mkArrow = (\p x y -> Arrow x y p) <$> arbitrarySourcePos



----------------------------------------------------
-- Smart constructors for non recursive values
----------------------------------------------------

mkNRAtom :: Gen AtomGen
mkNRAtom = AtomGen <$> oneof
  [ mkVal <*> arbitrary
  , mkVar <*> arbitrary
  ]

mkNRTerm :: Gen TermGen
mkNRTerm = TermGen . OfAtom . coerce <$> mkNRAtom

mkNRExpr :: Gen ExprGen
mkNRExpr = ExprGen . OfTerm . coerce <$> mkNRTerm

mkNRTypes0 :: Gen Types0Gen
mkNRTypes0 = Types0Gen <$> mkZ

mkNRTypes :: Gen TypesGen
mkNRTypes = TypesGen . OfTypes0 . coerce <$> mkNRTypes0

--------------------------
-- Custom Generators
--------------------------

-- | Generates valid Zilly identifiers
newtype IdentifierGen = IdentifierGen String deriving newtype Show

newtype SizedExprGen = SizedExprGen ExprGen deriving newtype Show

newtype Depth = Depth Int
  deriving Show
  deriving newtype (Eq,Ord,Num)

newtype Width = Width Int
  deriving Show
  deriving newtype (Eq,Ord,Num)


sizedExpr :: Depth -> Gen ExprGen
sizedExpr 0  = mkNRExpr
sizedExpr d = do
  let d' = d-1
  ExprGen <$> oneof
    [ mkMinus  <*> coerce (sizedExpr d') <*> coerce (sizedTerm d')
    , mkLess   <*> coerce (sizedExpr d') <*> coerce (sizedTerm d')
    , mkOfTerm <*> coerce (sizedTerm d')
    ]


sizedTerm :: Depth -> Gen TermGen
sizedTerm 0 = mkNRTerm
sizedTerm d = do
  let d' = d-1
  TermGen <$> oneof
    [ mkApp    <*> coerce (sizedTerm d') <*> coerce (sizedExpr d')
    , mkOfAtom <*> coerce (sizedAtom d')
    ]

-- (Expr -> Atom) -> (Expr -> Expr)
-- Gen (Expr -> Atom)
sizedAtom :: Depth -> Gen AtomGen
sizedAtom 0 = mkNRAtom
sizedAtom d = do
  let d' = d-1
  AtomGen <$> oneof
    [ mkParens     <*> coerce (sizedExpr d')
    , mkDefer      <*> coerce (sizedExpr d')
    , mkFormula    <*> (fmap (OfTerm . OfAtom) <$> mkParens <*> coerce (sizedExpr d'))
    , mkIfThenElse <*> coerce (sizedExpr d') <*> coerce (sizedExpr d') <*> coerce (sizedExpr d')
    -- TODO sized Types
    --, mkLambda     <*> arbitrary <*> fmap (coerce @TypesGen) arbitrary <*> coerce (sizedExpr d')
    ]

sizedTypes :: Depth ->  Gen TypesGen
sizedTypes 0 = mkNRTypes
sizedTypes d = do
  let d' = d-1
  TypesGen <$> oneof
    [ mkArrow <*> coerce (sizedTypes0 d') <*> coerce (sizedTypes d')
    , coerce mkNRTypes
    ]

sizedTypes0 :: Depth  -> Gen Types0Gen
sizedTypes0 0 = mkNRTypes0
sizedTypes0 d = do
  let d' = d-1
  Types0Gen <$> oneof
    [ mkLazy   <*> coerce (sizedTypes d')
    , mkTParen <*> coerce (sizedTypes d')
    ]




---------------------------------
-- Arbitrary newtype unwrapping
---------------------------------

arbitraryExpr :: Gen Expr
arbitraryExpr = fmap (coerce @ExprGen) arbitrary

arbitraryTerm :: Gen Term
arbitraryTerm = fmap (coerce @TermGen) arbitrary

arbitraryAtom :: Gen Atom
arbitraryAtom = fmap (coerce @AtomGen) arbitrary

arbitraryTypes :: Gen Types
arbitraryTypes = fmap (coerce @TypesGen) arbitrary

arbitraryTypes0 :: Gen Types0
arbitraryTypes0 = fmap (coerce @Types0Gen) arbitrary

arbitraryA0 :: Gen A0
arbitraryA0 = fmap (coerce @A0Gen) arbitrary

arbitraryA1 :: Gen A1
arbitraryA1 = fmap (coerce @A1Gen) arbitrary

arbitraryIdentifier :: Gen String
arbitraryIdentifier = fmap (coerce @IdentifierGen) arbitrary

arbitrarySourcePos :: Gen SourcePos
arbitrarySourcePos = pure $ initialPos ""


---------------------------------
-- Arbitrary instances
---------------------------------

instance Arbitrary IdentifierGen where
  arbitrary = fmap IdentifierGen . sized
    $ withMaxLength maxIdentLength (\n -> take (abs n + 1) <$> identifier)
    where
      firstChar = elements  $ '_' : ['a'..'z']
      rest = listOf . elements $ '_' : ['a'..'z'] <> ['0'..'9']
      identifier = liftA2 (:) firstChar rest



instance Arbitrary ExprGen where
  arbitrary = sized (withMaxLength maxDepth (sizedExpr . coerce))

instance Arbitrary TermGen where
  arbitrary = sized (withMaxLength maxDepth (sizedTerm . coerce))

instance Arbitrary AtomGen where
  arbitrary = sized (withMaxLength maxDepth (sizedAtom . coerce))


instance Arbitrary TypesGen where
    arbitrary = sized (withMaxLength maxDepth (sizedTypes . coerce))


instance Arbitrary Types0Gen where
  arbitrary = sized (withMaxLength maxDepth (sizedTypes0 . coerce))

instance Arbitrary A0Gen where
  arbitrary = A0Gen <$> oneof
    [ Decl   <$> arbitraryTypes <*> arbitraryIdentifier     <*> arbitraryExpr <*> arbitrarySourcePos
    , Assign <$> arbitraryIdentifier      <*> arbitraryExpr <*> arbitrarySourcePos
    , Print  <$> arbitraryExpr  <*> arbitrarySourcePos
    ]

instance Arbitrary A1Gen where
  arbitrary = fmap A1Gen . frequency $ zip [1,4]
    [ Seq  <$> arbitraryA0 <*> sized (\n -> take n <$> listOf arbitraryA0)
    , OfA0 <$> arbitraryA0
    ]

testExprParser :: Property
testExprParser = forAll arbitraryExpr $ \e ->
  case parseExpr (show $ P defaultPSC e) of
    Left _ -> counterexample ("Can't Parse:\n" <> show (P defaultPSC e)) False
    Right e' -> property True

props :: [Property]
props =
  [testExprParser]