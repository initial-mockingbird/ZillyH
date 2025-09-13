{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE GADTs               #-}

module Zilly.Puzzle.TypeCheck.ExtensionCheck
  ( Extensions(..)
  , ExtensionCheckEff(..)
  , extensionCheckE
  , extensionCheckA0
  , extensionCheckA1
  , extensionCheckTypes

  ) where

import Zilly.Puzzle.Parser
import Zilly.Puzzle.Types.Exports qualified as T


import Prelude.Singletons
import Data.Singletons.TH
import Data.Matchers
import Data.Traversable

data Extensions
  = InfixFunctions
  | BoolType
  | RealType
  | TupleType
  | StringType
  | ArrayType
  | MultiParamApp
  | MultiParamLambda
  | ExtendedPrelude
  | UserDefinedTypes
  | GenericTypes
  deriving (Eq, Ord)

instance Show Extensions where
  show InfixFunctions = "Infix Functions"
  show BoolType = "Bool Type"
  show RealType = "Real Type"
  show TupleType = "Tuple Type"
  show StringType = "String Type"
  show ArrayType = "Array Type"
  show MultiParamApp = "Multi-Parameter Application"
  show MultiParamLambda = "Multi-Parameter Lambda"
  show ExtendedPrelude = "Extended Prelude"
  show UserDefinedTypes = "User-Defined Types"
  show GenericTypes = "Generic Types"


class Monad m => ExtensionCheckEff m where
  validateExtension :: Extensions -> BookeepInfo -> m ()
  getEnabledExtensions :: m [Extensions]

extensionCheckTypes :: forall m .
  ( ExtensionCheckEff m
  )
  => BookeepInfo
  -> T.Types
  -> m T.Types
extensionCheckTypes bk (T.NDArray n a) = do
  validateExtension ArrayType bk
  a' <- extensionCheckTypes bk a
  pure (T.NDArray n a')
extensionCheckTypes bk (T.ARecord fields) = do
  validateExtension UserDefinedTypes bk
  fields' <- for fields $ \(k,v) -> do
    v' <- extensionCheckTypes bk v
    pure (k,v')
  pure (T.ARecord fields')
extensionCheckTypes bk (T.Tuple a b) = do
  validateExtension TupleType bk
  a' <- extensionCheckTypes bk a
  b' <- extensionCheckTypes bk b
  pure (T.Tuple a' b')
extensionCheckTypes bk T.F = do
  validateExtension RealType bk
  pure T.F
extensionCheckTypes bk (T.ZString) = do
  validateExtension StringType bk
  pure T.ZString
extensionCheckTypes bk (T.ZBool) = do
  validateExtension BoolType bk
  pure T.ZBool
extensionCheckTypes bk (a T.:-> b) = do
  a' <- extensionCheckTypes bk a
  b' <- extensionCheckTypes bk b
  pure (a' T.:-> b')
extensionCheckTypes bk (T.TVar v) = do
  validateExtension GenericTypes bk
  pure (T.TVar v)
extensionCheckTypes bk (T.TFamApp name t args) = do
  validateExtension UserDefinedTypes bk
  t' <- extensionCheckTypes bk t
  args' <- traverse (extensionCheckTypes bk) args
  pure (T.TFamApp name t' args')
extensionCheckTypes _ a = pure a


extensionCheckA0 :: forall m.
  ( ExtensionCheckEff m
  )
  => A0 ParsingStage
  -> m (A0 ParsingStage)
extensionCheckA0 (Decl t l r bk) = do
  t' <- extensionCheckTypes bk t
  l' <- extensionCheckE l
  r' <- extensionCheckE r
  pure (Decl t' l' r' bk)
extensionCheckA0 (Assign l r bk) = do
  l' <- extensionCheckE l
  r' <- extensionCheckE r
  pure (Assign l' r' bk)
extensionCheckA0 (Print e bk) = do
  e' <- extensionCheckE e
  pure (Print e' bk)
extensionCheckA0 (SysCommand s bk) = pure $ SysCommand s bk
extensionCheckA0 (PTypeDef name fields  bk) = do
  validateExtension UserDefinedTypes bk
  pure (PTypeDef name fields bk)

extensionCheckA1 :: forall m.
  ( ExtensionCheckEff m
  )
  => A1 ParsingStage
  -> m (A1 ParsingStage)
extensionCheckA1 (Seq bk a as) = do
  a' <- extensionCheckA0 a
  as' <- traverse extensionCheckA0 as
  pure (Seq bk a' as')
extensionCheckA1 (OfA0 a) = do
  a' <- extensionCheckA0 a
  pure (OfA0 a')


extensionCheckE :: forall n m.
  ( ExtensionCheckEff m
  , SingI n
  )
  => EPrec ParsingStage n
  -> m (EPrec ParsingStage n)
extensionCheckE e = case () of
  () | Just Refl <- matches @0 (sing @n) -> extensionCheckE0 e
     | Just Refl <- matches @1 (sing @n) -> extensionCheckE1 e
     | Just Refl <- matches @3 (sing @n) -> extensionCheckE3 e
     | Just Refl <- matches @4 (sing @n) -> extensionCheckE5 e
     | Just Refl <- matches @6 (sing @n) -> extensionCheckE6 e
     | Just Refl <- matches @7 (sing @n) -> extensionCheckE7 e
     | Just Refl <- matches @8 (sing @n) -> extensionCheckE8 e
     | Just Refl <- matches @(PostfixPrec ) (sing @n) -> extensionCheckEPostfix e
     | Just Refl <- matches @(PrefixPrec ) (sing @n) -> extensionCheckEPrefix e
     | Just Refl <- matches @(Atom ) (sing @n) -> extensionCheckEAtom e
     | otherwise -> error $ "ExtensionCheck: No match for " ++ show (sing @n) ++ " in " ++ show e


extensionCheckEAtom ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage Atom
  -> m (EPrec ParsingStage Atom)
extensionCheckEAtom (PInt bk a) = pure $ PInt bk a
extensionCheckEAtom (PFloat bk a) =
  validateExtension RealType bk >> pure (PFloat bk a)
extensionCheckEAtom (PString bk a) =
  validateExtension StringType bk >> pure (PString bk a)
extensionCheckEAtom (PBool bk a) =
  validateExtension BoolType bk >> pure (PBool bk a)
extensionCheckEAtom (PVar bk a) = pure (PVar bk a)
extensionCheckEAtom (PArray bk xs) = do
  -- validateExtension ArrayType bk
  xs' <- traverse extensionCheckE xs
  pure (PArray bk xs')
extensionCheckEAtom (PTuple bk a b xs) = do
  validateExtension TupleType bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  xs' <- traverse extensionCheckE xs
  pure (PTuple bk a' b' xs')
extensionCheckEAtom (PParen bk a) = do
  a' <- extensionCheckE a
  pure (PParen bk a')
extensionCheckEAtom (PDefer bk a) = do
  a' <- extensionCheckE a
  pure (PDefer bk a' )
extensionCheckEAtom (PIf bk (a, b, c)) = do
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  c' <- extensionCheckE c
  pure (PIf bk (a', b', c'))
extensionCheckEAtom (PMatch bk e patternsE) = do
  validateExtension UserDefinedTypes bk
  e' <- extensionCheckE e
  patternsE' <- for patternsE $ \(pat, expr') -> do
    expr'' <- extensionCheckE expr'
    pure (pat, expr'')
  pure (PMatch bk e' patternsE')
extensionCheckEAtom (PECons bk s es) = do
  validateExtension UserDefinedTypes bk
  es' <- traverse extensionCheckE es
  pure (PECons bk s es')
extensionCheckEAtom (PEARecord  bk fields) = do
  validateExtension UserDefinedTypes bk
  fields' <- for fields $ \(k,v) -> do
    v' <- extensionCheckE v
    pure (k,v')
  pure (PEARecord bk fields')

extensionCheckEPrefix ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage PrefixPrec
  -> m (EPrec ParsingStage PrefixPrec)
extensionCheckEPrefix (PUMinus bk a) = do
  a' <- extensionCheckE a
  pure (PUMinus bk a')
extensionCheckEPrefix (PNegate bk a) = do
  a' <- extensionCheckE a
  pure (PNegate bk a')
extensionCheckEPrefix (OfHigherPrefixPrec a) = do
  a' <- extensionCheckE a
  pure (OfHigherPrefixPrec a')

extensionCheckEPostfix ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage PostfixPrec
  -> m (EPrec ParsingStage PostfixPrec)
extensionCheckEPostfix (PApp bk a xs@(_:_:_)) = do
  validateExtension MultiParamApp bk
  a' <- extensionCheckE a
  xs' <- traverse extensionCheckE xs
  pure (PApp bk a' xs')
extensionCheckEPostfix (PApp bk a xs) = do
  a' <- extensionCheckE a
  xs' <- traverse extensionCheckE xs
  pure (PApp bk a' xs')
extensionCheckEPostfix (PAppArr bk a xs) = do
  validateExtension ArrayType bk
  a' <- extensionCheckE a
  xs' <- traverse extensionCheckIndexer xs
  pure (PAppArr bk a' xs')
extensionCheckEPostfix (OfHigherPostfixPrec a) = do
  a' <- extensionCheckE a
  pure (OfHigherPostfixPrec a')
extensionCheckEPostfix (PDotApp bk e field) = do
  validateExtension UserDefinedTypes bk
  e' <- extensionCheckE e
  pure (PDotApp bk e' field)

extensionCheckIndexer ::
  ( ExtensionCheckEff m
  )
  => PIndexerExpression ParsingStage
  -> m (PIndexerExpression ParsingStage)
extensionCheckIndexer (PIndex a) = PIndex <$> extensionCheckE a
extensionCheckIndexer (PRangeIndexer (a,b)) =
  PRangeIndexer <$> ((,) <$> extensionCheckE a <*> extensionCheckE b)

extensionCheckE8 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 8
  -> m (EPrec ParsingStage 8)
extensionCheckE8 (PPower bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PPower bk a' b')
extensionCheckE8 (OfHigher8 a) = do
  a' <- extensionCheckE a
  pure (OfHigher8 a')


extensionCheckE7 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 7
  -> m (EPrec ParsingStage 7)
extensionCheckE7 (PMul bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PMul bk a' b')
extensionCheckE7 (PDiv bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PDiv bk a' b')
extensionCheckE7 (PMod bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PMod bk a' b')
extensionCheckE7 (OfHigher7 a) = do
  a' <- extensionCheckE a
  pure (OfHigher7 a')

extensionCheckE6 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 6
  -> m (EPrec ParsingStage 6)
extensionCheckE6 (PPlus bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PPlus bk a' b')
extensionCheckE6 (PMinus bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PMinus bk a' b')
extensionCheckE6 (PAppend bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PAppend bk a' b')
extensionCheckE6 (OfHigher6 a) = do
  a' <- extensionCheckE a
  pure (OfHigher6 a')


extensionCheckE5 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 4
  -> m (EPrec ParsingStage 4)
extensionCheckE5 (PLT bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PLT bk a' b')
extensionCheckE5 (PLTEQ bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PLTEQ bk a' b')
extensionCheckE5 (PGT bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PGT bk a' b')
extensionCheckE5 (PGTEQ bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PGTEQ bk a' b')
extensionCheckE5 (PEQ bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PEQ bk a' b')
extensionCheckE5 (PNEQ bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PNEQ bk a' b')
extensionCheckE5 (OfHigher4 a) = do
  a' <- extensionCheckE a
  pure (OfHigher4 a')

extensionCheckE3 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 3
  -> m (EPrec ParsingStage 3)
extensionCheckE3 (PAnd bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (PAnd bk a' b')
extensionCheckE3 (POr bk a b) = do
  validateExtension InfixFunctions bk
  a' <- extensionCheckE a
  b' <- extensionCheckE b
  pure (POr bk a' b')
extensionCheckE3 (OfHigher3 a) = do
  a' <- extensionCheckE a
  pure (OfHigher3 a')

extensionCheckE1 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 1
  -> m (EPrec ParsingStage 1)
extensionCheckE1 (PLambda bk args@(_:_:_) mret body) = do
  validateExtension MultiParamLambda bk
  args' <- for args $ \(e,t) -> do
    let bk = getBookeepInfo e
    e' <- extensionCheckE e
    t' <- extensionCheckTypes bk t
    pure (e', t')
  mret' <- traverse (extensionCheckTypes bk) mret
  body' <- extensionCheckE body
  pure (PLambda bk args' mret' body')
extensionCheckE1 (PLambda bk args mret body) = do
  args' <- for args $ \(e,t) -> do
    let bk = getBookeepInfo e
    e' <- extensionCheckE e
    t' <- extensionCheckTypes bk t
    pure (e', t')
  mret' <- traverse (extensionCheckTypes bk) mret
  body' <- extensionCheckE body
  pure (PLambda bk args' mret' body')
extensionCheckE1 (OfHigher1 a) = do
  a' <- extensionCheckE a
  pure (OfHigher1 a')

extensionCheckE0 ::
  ( ExtensionCheckEff m
  )
  => EPrec ParsingStage 0
  -> m (EPrec ParsingStage 0)
extensionCheckE0 (OfHigher0 a) = do
  a' <- extensionCheckE a
  pure (OfHigher0 a')
