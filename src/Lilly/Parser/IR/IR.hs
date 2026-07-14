{-|
Module      : Lilly.Parser.IR
Description : IR Data definitions for Lily.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

This module holds the data definitions for the abstract syntax which the concrete
syntax is parsed into. 

Methodology wise, the abstract syntax is defined using what's known as
"Base Functors". This allows for some flexibility when we decorate the tree
(refer to the Lilly.Parser.NewParser for an example of this).

-}

module Lilly.Parser.IR.IR where

import Data.Text (Text)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Fix
import Data.Bifunctor

-- | Dimention of an Array Type. Will always hold a positive integer. 
type Dimention = Int
-- | Attributes (i.e: ``foo.bar``) are represented as constant text. 
type Attribute = Text
-- | Constructor names are represented as constant text.
type ConstructorName = Text
-- | Operators are saved without leading or trailing whitespace.
type Operator = Text
{- | Lambda binders are text. Maybe we should rethink the syntax (take inspiration from OCaml) and
    allow for patterns there.
-}
type LambdaBinder = Text
-- | Identifiers are represented as constant text.
type Identifier = Text
-- | Type variables are represented as constant text. They all begin with an apostrophe (').
type TypeVariable = Text

-- | Base functor for the types in the language.
data TypesF a
    = PTZ
    | PTR
    | PTB
    | PTString
    | PTLazy a
    | PTArray Dimention a
    | PTNtuple (a,a) [a]
    | PTPolymorphic Text [a]
    | PTUserDefined Text [a]
    | PArrow a a

instance Functor TypesF where
    fmap _ PTZ = PTZ
    fmap _ PTR = PTR
    fmap _ PTB = PTB
    fmap _ PTString = PTString
    fmap f (PTLazy a) = PTLazy $ f a
    fmap f (PTArray d a) = PTArray d $ f a
    fmap f (PTNtuple (a1,a2) as) = PTNtuple (f a1, f a2) (fmap f as)
    fmap f (PTPolymorphic name as) = PTPolymorphic name (fmap f as)
    fmap f (PTUserDefined name as) = PTUserDefined name (fmap f as)
    fmap f (PArrow a1 a2) = PArrow (f a1) (f a2)

-- | The types in the language are represented as a fixed point of the base functor.
type Types = Fix TypesF

data Indexing a = Index a | Slice (a,a)

instance Functor Indexing where
    fmap f (Index a) = Index (f a)
    fmap f (Slice (a1,a2)) = Slice (f a1, f a2)

-- | Base functor for the expressions in the language.
data ExpressionF typesA patternA guardA a
    = PVariable Text
    | PInteger Integer
    | PFloat Double
    | PBoolean Bool
    | PString Text
    | PParen a
    | PArray [a]
    | PDefer a
    | PCall a [a]
    | PIndex a (NonEmpty (Indexing a))
    | PPrefix Operator a
    | PInfix a Operator a
    | PPostfix a Operator
    | PLambda (NonEmpty (LambdaBinder, typesA)) (Maybe typesA) a
    | PDot a Attribute
    | PMatch a (NonEmpty (patternA, [guardA],a))
    | PRecord [(Attribute, a)]
    | PNTuple (a,a) [a]
    | PClosure [(LambdaBinder,a)] a

{-|  The expressions in the language are represented as a fixed point of the base functor.
    We can't use a type synonym here because we have mutually recursive types (Expressions and Guards).
    Which fucks up type synonyms (mutually recursive type synonyms means there is no termination,
    since they are eagerly expanded). 
-}
newtype Expression = Expression {unExpr :: ExpressionF Types Pattern Guard Expression}

-- | Base functor for the patterns in the language.
data PatternF a
    = PPVariable Text
    | PPInteger Integer
    | PPFloat Double
    | PPBoolean Bool
    | PPString Text
    | PPArray [a]
    | PPConstructorRecord ConstructorName [(Attribute, a)]
    | PPConstructorAnon ConstructorName [a]
    | PPRecord [(Attribute,a)]

instance Functor PatternF where
    fmap _ (PPVariable name) = PPVariable name
    fmap _ (PPInteger i) = PPInteger i
    fmap _ (PPFloat d) = PPFloat d
    fmap _ (PPBoolean b) = PPBoolean b
    fmap _ (PPString s) = PPString s
    fmap f (PPArray ps) = PPArray (fmap f ps)
    fmap f (PPConstructorRecord name fields) = PPConstructorRecord name (fmap (second f) fields)
    fmap f (PPConstructorAnon name ps) = PPConstructorAnon name (fmap f ps)
    fmap f (PPRecord fields) = PPRecord (fmap (second f) fields)

-- | The patterns in the language are represented as a fixed point of the base functor.
type Pattern = Fix PatternF

-- | Base functor for the guards in the language.
data GuardF patternA expressionA a
    = PGExpression expressionA
    | PGPattern patternA expressionA

-- | The guards in the language are represented as a fixed point of the base functor.
newtype Guard = Guard {unGuard :: GuardF Pattern Expression ()}

-- | Base functor for the actions in the language.
data ActionF typesA  expressionA productTypesA a
    = PAExpression expressionA
    | PASysCommand Text [expressionA]
    | PADef typesA Identifier expressionA
    | PAReassign Identifier expressionA
    | PATypeDef Identifier [TypeVariable] [(ConstructorName, [productTypesA])]
    | PModeChange Text

{- |
    A "general" Functor for the base functor of the actions in the language. 
    Allows for mapping over all the possible types in the base functor.
-}
class ActionFunctor f where
    mapActionF
        :: (typesA -> typesB)
        -> (expressionA -> expressionB)
        -> (productTypesA -> productTypesB)
        -> (a -> b)
        -> f typesA expressionA productTypesA a
        -> f typesB expressionB productTypesB b

instance ActionFunctor ActionF where
    mapActionF _  exprF _ _ (PAExpression e) = PAExpression $ exprF e
    mapActionF _  exprF _ _ (PASysCommand cmd args) = PASysCommand cmd $ exprF <$> args
    mapActionF typesF  exprF _ _ (PADef t name e) = PADef (typesF t) name $ exprF e
    mapActionF _  exprF _ _ (PAReassign name e) = PAReassign name $ exprF e
    mapActionF _  _ productTypesF _ (PATypeDef name typeVars constructors) =
        PATypeDef name typeVars $ fmap (second (fmap productTypesF)) constructors
    mapActionF _ _ _ _ (PModeChange mode) = PModeChange mode

instance Functor (ActionF typesA expressionA productTypesA) where
    fmap = mapActionF id id id

newtype Action = Action {unAction :: ActionF Types Expression ProductTypes ()}

-- | Base functor for the product types in the language.
data ProductTypesF typesA a
    = PTProduct [typesA]
    | PTRecord [(Attribute, typesA)]

newtype ProductTypes = ProductTypes {unProductTypes :: ProductTypesF Types ()}


{- | 
    A "general" Functor for the base functor of the product types in the language. 
    Allows for mapping over all the possible types in the base functor.
-}
class ProductTypesFunctor f where
    mapProductTypesF
        :: (typesA -> typesB)
        -> (a -> b)
        -> f typesA a
        -> f typesB b

instance ProductTypesFunctor ProductTypesF where
    mapProductTypesF f _ (PTProduct ts) = PTProduct $ f <$> ts
    mapProductTypesF typesF _ (PTRecord fields) = PTRecord (fmap (second typesF) fields)
instance Functor (ProductTypesF typesA) where
    fmap  = mapProductTypesF id

{-| 
    A "general" Functor for the base functor of the expressions in the language. 
    Allows for mapping over all the possible types in the base functor.
-}
class ExpressionFunctor f where
    mapExpressionF
        :: (typesA -> typesB)
        -> (patternA -> patternB)
        -> (guardA -> guardB)
        -> (a -> b)
        -> f typesA patternA guardA a
        -> f typesB patternB guardB b

instance ExpressionFunctor ExpressionF where
    mapExpressionF _ _ _ _ (PVariable name) = PVariable name
    mapExpressionF _ _ _ _ (PInteger i) = PInteger i
    mapExpressionF _ _ _ _ (PFloat d) = PFloat d
    mapExpressionF _ _ _ _ (PBoolean b) = PBoolean b
    mapExpressionF _ _ _ _ (PString s) = PString s
    mapExpressionF _ _ _ f (PParen a) = PParen (f a)
    mapExpressionF _ _ _ f (PArray as) = PArray (fmap f as)
    mapExpressionF _ _ _ f (PDefer a) = PDefer (f a)
    mapExpressionF _ _ _ f (PCall a as) = PCall (f a) (fmap f as)
    mapExpressionF _ _ _ f (PIndex a idxs) = PIndex (f a) (fmap f <$> idxs)
    mapExpressionF _ _ _ f (PPrefix op a) = PPrefix op (f a)
    mapExpressionF _ _ _ f (PInfix a1 op a2) = PInfix (f a1) op (f a2)
    mapExpressionF typesF _ _ f (PLambda binders retType body) = PLambda (fmap (second typesF) binders) (fmap typesF retType) (f body)
    mapExpressionF _ _ _ f (PDot a attr) = PDot (f a) attr
    mapExpressionF _ patternF guardF f (PMatch a cs) = PMatch (f a) (fmap (\(p, gs, e) -> (patternF p, fmap guardF gs, f e)) cs)
    mapExpressionF _ _ _ f (PRecord fields) = PRecord (fmap (second f) fields)
    mapExpressionF _ _ _ f (PNTuple (a1,a2) as) = PNTuple (f a1, f a2) (fmap f as)
    mapExpressionF _ _ _ f (PClosure binders body) = PClosure (fmap (second f) binders) (f body)
    mapExpressionF _ _ _ f (PPostfix a op) = PPostfix (f a) op

instance Functor (ExpressionF typesA patternA guardA) where
    fmap  = mapExpressionF id id id

{- |
    A "general" Functor for the base functor of the guards in the language. 
    Allows for mapping over all the possible types in the base functor.
-}
class GuardFunctor f where
    mapGuardF
        :: (patternA -> patternB)
        -> (expressionA -> expressionB)
        -> (a -> b)
        -> f patternA expressionA a
        -> f patternB expressionB b

instance GuardFunctor GuardF where
    mapGuardF  _ exprF _  (PGExpression e) = PGExpression $ exprF  e
    mapGuardF  patternF exprF _  (PGPattern p e) = PGPattern
        (patternF p)
        (exprF  e)

instance Functor (GuardF patternA expressionA) where
    fmap = mapGuardF id id