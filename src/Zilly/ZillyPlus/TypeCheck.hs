
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeAbstractions           #-}

module Zilly.ZillyPlus.TypeCheck where


import Parser.ClassicPlus.ZillyPlusParser qualified as P
import Utilities.LensM
import Utilities.TypedMapPlus hiding (empty)
import Utilities.ShowM
import Zilly.ADT.ExpressionPlus
import Zilly.ADT.ActionPlus
import Zilly.ZillyPlus.Expression
import Zilly.ADT.Error 
import Zilly.ZillyPlus.Error 
import Zilly.ADT.Array 
import Zilly.ZillyPlus.Array  
import Zilly.ADT.Arithmetic 
import Zilly.ZillyPlus.Arithmetic
import Zilly.ZillyPlus.Tower
import Zilly.ZillyPlus.Interpreter hiding (Env)
import Zilly.RValuePlus
import Zilly.Types
import Zilly.UpcastPlus
import Control.Monad.Reader
import Data.Proof

import Data.Kind (Type)
import Prelude.Singletons hiding (Map,Symbol,Seq)
import Control.Monad.IO.Class (MonadIO)
import Control.Applicative (Alternative(..), Const(..))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Writer.CPS
import Control.Monad.Error.Class
import Control.Monad.Trans.Maybe
import Parser.ClassicPlus.ZillyPlusParser qualified as P
import Control.Monad (join)
import Text.Parsec (SourcePos)
import Data.Singletons.Decide
import Data.Traversable
import GHC.TypeLits.Singletons hiding (Symbol)
import Data.Type.Equality
import Data.Maybe (fromMaybe) 
import Data.Sequence hiding (empty) 
import Data.Nat
import Data.Maybe (fromJust)

type Some :: forall k. (k -> Type) -> Type 
data Some (f :: k -> Type) where
    MkSome :: forall {k} f (a :: k). SingI a => f a -> Some f

data TypeCheckEnv = TCE 
  { varMapping :: Map Symbol Types
  , expectedType :: Maybe Types
  }
type ErrorLog = [TypeCheckErrors]

newtype ExpectedType = ExpectedType Types deriving newtype Show
newtype GotType      = GotType      Types deriving newtype Show

data TypeCheckErrors 
  = SymbolNotDefined Symbol SourcePos
  | FormulaNeedsLValue P.Expr SourcePos
  | TypeMismatch ExpectedType GotType SourcePos
  | NonUnifiableTypes (Types,SourcePos) (Types,SourcePos)
  | ArgNotSubtype    (Types,SourcePos) Types
  | ArgIsNotStrictSubtype   (Types,SourcePos) Types
  | AppNotAFun Types SourcePos
  | RHSNotSubtype    (Types,SourcePos) Types
  | RHSIsNotStrictSubtype   (Types,SourcePos) Types

instance Show TypeCheckErrors where
  show (SymbolNotDefined s pos) = "Symbol " <> show s <> " not defined " <> show pos
  -- show (FormulaNeedsLValue e pos) = "Needs lvalue " <> show e <> " " <> show pos 
  show (TypeMismatch t1 t2 pos) = "Type mismatch " <> show pos
  show (NonUnifiableTypes (t1,pos1) (t2,pos2) ) 
    = "Non unifiable types:\n" 
      <> show t1 <> "(" <> show pos1 <> ")\n" 
      <> show t2 <> "(" <> show pos2 <> ")\n" 
  show (ArgNotSubtype (t,s) expected) 
    = "Value passed as argument is not a subtype of the argument.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (ArgIsNotStrictSubtype (t,s) expected) 
    = "Value passed as argument is not a strict subtype of the argument.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (AppNotAFun t s) 
    = "Left argument of function application is not a function. Expected type: " <> show t <> " " <> show s
  show (RHSNotSubtype (t,s) expected) 
    = "Right hand side of assignment is not a subtype of the left hand side.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s
  show (RHSIsNotStrictSubtype (t,s) expected) 
    = "Right hand side of assignment is not a strict subtype of the left hand side.\n"
      <> "Expected: " <> show expected <> "\n"
      <> "But instead got: " <> show t <> " " <> show s


newtype TCM a = TCM { unTCM :: ReaderT TypeCheckEnv (MaybeT (Writer ErrorLog) ) a }
  deriving newtype 
    ( Functor
    , Applicative
    , Monad
    , MonadReader TypeCheckEnv
    , MonadWriter ErrorLog
    , Alternative
    , MonadFail
    )



data TcGen  = TcGen
  { tcGenEnv :: TypeCheckEnv
  , tcGenPos :: SourcePos 
  }


class TypeCheck actx e ret | e -> ret where
  type TCC actx ret :: ret -> Type
  type TCReturn actx e :: Type 
  typeCheck :: forall {f} .
    ( TCC actx ret ~ f
    ) => e -> TCM (Some f,TCReturn actx e)



instance SingI n => TypeCheck ActionTag (P.EPrec n) Types where 
  type TCC ActionTag Types = ET 
  type TCReturn ActionTag  (P.EPrec n) = TcGen

  typeCheck a = fromMaybe undefined $ handleAtoms a 
 
instance  TypeCheck ActionTag P.A0 () where
  type TCC ActionTag () = Const' (A ActionTag)
  type TCReturn ActionTag P.A0 = TcGen 

  typeCheck (P.Decl t l r _) = handleAssign t l r
  typeCheck (P.Assign v e _) = handleReassign v e 
  typeCheck (P.Print e _)   = typeCheck @ActionTag e  >>= \(MkSome e',env) -> pure 
    (MkSome . Const' @_ @'() . PrintE $ e', env)



newtype Const' a (b :: ()) = Const' {getConst' :: a}

data ExistLensM where 
  MkExistsLensM :: SingI a => LensM (AssocCtxMonad ActionTag) (E Void2 ErrorT ExprTag a) -> ExistLensM 

buildNestedLens :: [Some ET] -> ExistLensM -> Maybe ExistLensM 
buildNestedLens [] l = pure l 
buildNestedLens (MkSome @_ @i' i' : sixs) (MkExistsLensM @a l) = case sing @a of 
  SArray @sa sa -> withSingI sa $ do 
    let
        mi :: (AssocCtxMonad ExprTag) Int
        mi = case sing @i' of 
          SValue SZ -> rvalue i' >>= \case 
            ETower (ValE n) -> pure n
            _ -> error "TODO"
          _ -> error "TODO"
        getL' :: Gamma (AssocCtxMonad ActionTag) 
          -> (AssocCtxMonad ActionTag) (E Void2 ErrorT ExprTag sa)
        getL' env = mi >>= \ix -> viewM l env >>= \case  
          (ExpE (ErrorT (ErrorExpE (ArrayT (ArrayLiteralE xs))))) 
            -> maybe 
              (error "TODO")  
              (pure . ExpE . ErrorT . ErrorExpE . ArrayT)
              $ xs !? ix 
          _ -> error "Impossible Case"

        setL' :: Gamma (AssocCtxMonad ActionTag) 
          -> E Void2 ErrorT ExprTag sa
          -> (AssocCtxMonad ActionTag) (Gamma (AssocCtxMonad ActionTag))
        setL' env x = mi >>= \ix -> viewM l env >>= \case  
          (ExpE (ErrorT (ErrorExpE (ArrayT (ArrayLiteralE xs))))) -> case xs !? ix of 
            Nothing -> error "TODO"
            Just _  -> setL l env . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
              $ update ix (ArrayInhE . ErrorT . ErrorInhE . ETower $  x) xs
          _ -> error "Impossible Case"

        setFL' _ _ = error "TODO"

        l' :: LensM (AssocCtxMonad ActionTag) (E Void2 ErrorT ExprTag sa)
        l' = LensM getL' setL' setFL' $ varNameM l

    buildNestedLens sixs (MkExistsLensM l')
  _ -> Nothing 


handleAssign :: forall n' n e. 
  ( SingI n 
  , SingI e
  , SingI n'
  ) => P.TPrec n' -> P.EPrec n -> P.EPrec e -> TCM (Some (Const' (A ActionTag)), TcGen)
handleAssign t a e
  | (Just Refl, P.PVar bk varName) <- (testEquality (sing @n) (sing @P.Atom),a) = do 
      env <- ask 
      let
        t' = fromJust $ P.parserT2ZT t
        env' = env{varMapping= M.insert varName (rValueT t') $ varMapping env, expectedType=Just t'}
      (MkSome @_ @e' e', _) <- local (const env') $ typeCheck @ActionTag e
      (MkSome @_ @var (ETower (VarE var)),_) <- local (const env') 
        $ typeCheck @ActionTag (P.PVar bk varName) 
      withSingIRType @e'
        $ withSingIRType @var 
        $ case upcastable @(RValueT var) @(RValueT e') @E @Void2 @ErrorT @ExprTag of 
          SameTypeUB _ -> let co :: Const' (A ActionTag) '() = Const' (AssignE var e') in pure 
            ( MkSome co
            , TcGen env $ P.tokenPos bk 
            )
          LeftUB _ -> let co :: Const' (A ActionTag) '() = Const' (AssignE var e') in pure 
            ( MkSome co
            , TcGen env $ P.tokenPos bk 
            )
          RightUB _         -> error "TODO"
          SomethingElseUB _ -> error "TODO"
          NonExistentUB     -> error "TODO"
  | (Just Refl, P.OfHigherPrefixPrec n) <- (testEquality (sing @n) (sing @P.PrefixPrec),a) = handleAssign t n e
  | (Just Refl, P.OfHigherPostfixPrec n) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = handleAssign t n e
  | (Just Refl, P.OfHigher8 n) <- (testEquality (sing @n) (sing @8),a) = handleAssign t n e
  | (Just Refl, P.OfHigher7 n) <- (testEquality (sing @n) (sing @7),a) = handleAssign t n e
  | (Just Refl, P.OfHigher6 n) <- (testEquality (sing @n) (sing @6),a) = handleAssign t n e
  | (Just Refl, P.OfHigher4 n) <- (testEquality (sing @n) (sing @4),a) = handleAssign t n e
  | (Just Refl, P.OfHigher0 n) <- (testEquality (sing @n) (sing @0),a) = handleAssign t n e
  | otherwise = error "TODO"


handleReassign :: forall n e. 
  ( SingI n 
  , SingI e
  ) => P.EPrec n -> P.EPrec e -> TCM (Some (Const' (A ActionTag)), TcGen)
handleReassign a e
  | (Just Refl, P.PVar bk varName) <- (testEquality (sing @n) (sing @P.Atom),a) = do 
      (MkSome @_ @var (ETower (VarE l)), _) <- typeCheck @ActionTag (P.PVar bk varName )
      (MkSome @_ @e' e', _) <- local (\env -> env{expectedType= Just (demote @var) }) 
        $ typeCheck @ActionTag e
      env <- ask 
      withSingIRType @e'
        $ withSingIRType @var 
        $ case upcastable @(RValueT var) @(RValueT e') @E @Void2 @ErrorT @ExprTag of 
          SameTypeUB _ -> let co :: Const' (A ActionTag) '() = Const' (ReassignE l e') in pure 
            ( MkSome co
            , TcGen env $ P.tokenPos bk 
            )
          LeftUB _ -> let co :: Const' (A ActionTag) '() = Const' (ReassignE l e') in pure 
            ( MkSome co
            , TcGen env $ P.tokenPos bk 
            )
          RightUB _         -> error "TODO"
          SomethingElseUB _ -> error "TODO"
          NonExistentUB     -> error "TODO"
  | (Just Refl, P.OfHigherPrefixPrec n) <- (testEquality (sing @n) (sing @P.PrefixPrec),a) = handleReassign n e
  | (Just Refl, P.OfHigherPostfixPrec n) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = handleReassign n e
  | (Just Refl, P.OfHigher8 n) <- (testEquality (sing @n) (sing @8),a) = handleReassign n e
  | (Just Refl, P.OfHigher7 n) <- (testEquality (sing @n) (sing @7),a) = handleReassign n e
  | (Just Refl, P.OfHigher6 n) <- (testEquality (sing @n) (sing @6),a) = handleReassign n e
  | (Just Refl, P.OfHigher4 n) <- (testEquality (sing @n) (sing @4),a) = handleReassign n e
  | (Just Refl, P.OfHigher0 n) <- (testEquality (sing @n) (sing @0),a) = handleReassign n e
  | (Just Refl, P.PAppArr bk arr []) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = case getVar arr of 
      Just varName -> handleReassign (P.PVar bk varName) e
      Nothing -> handleReassign arr e
  | (Just Refl, P.PAppArr bk (P.PAppArr _ arr xs) (y:ys)) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) 
      = handleReassign (P.PAppArr bk arr $ xs <> (y:ys)) e

  | (Just Refl, P.PAppArr bk arr args) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = do 
      varName <- maybe (error "TODO") pure $ getVar arr
      (MkSome @_ @var (ETower (VarE l)), _) <- typeCheck @ActionTag (P.PVar bk varName )
      is  <- traverse (\(P.MkTupleArg _ i) -> fst <$> typeCheck @ActionTag i) args
      MkExistsLensM @sa l' <- maybe (error "TODO") pure $ buildNestedLens is $ MkExistsLensM l
      (MkSome @_ @e' e', _) <- local (\env -> env{expectedType= Just (demote @sa) }) 
          $ typeCheck @ActionTag e

      env <- ask
      withSingIRType @e'
        $ withSingIRType @sa
        $ case upcastable @(RValueT sa) @(RValueT e') @E @Void2 @ErrorT @ExprTag of 
          SameTypeUB _ -> let co :: Const' (A ActionTag) '() = Const' (ReassignE l' e') in pure 
            ( MkSome co
            , TcGen env $ P.tokenPos bk 
            ) 
          LeftUB _ -> let co :: Const' (A ActionTag) '() = Const' (ReassignE l' e') in pure 
            ( MkSome co
            , TcGen env $ P.tokenPos bk 
            ) 

          RightUB _         -> error "TODO"
          SomethingElseUB _ -> error "TODO"
          NonExistentUB     -> error "TODO"
  | otherwise = error "TODO"


getVar :: forall n. SingI n => P.EPrec n -> Maybe String 
getVar a 
  | Just Refl <- testEquality (sing @n) (sing @P.Atom) = case a of 
    P.PVar _ varName -> pure varName
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @P.PrefixPrec) = case a of 
    P.OfHigherPrefixPrec a' -> getVar a'
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @P.PostfixPrec) = case a of 
    P.OfHigherPostfixPrec a' -> getVar a'
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @8) = case a of 
    P.OfHigher8 a' -> getVar a'
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @7) = case a of 
    P.OfHigher7 a' -> getVar a'
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @6) = case a of 
    P.OfHigher6 a' -> getVar a'
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @4) = case a of 
    P.OfHigher4 a' -> getVar a'
    _ -> Nothing 
  | Just Refl <- testEquality (sing @n) (sing @0) = case a of 
    P.OfHigher0 a' -> getVar a'

  | otherwise = Nothing




handleAtoms :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handleAtoms a = testEquality (sing @n) (sing @P.Inf) >>= \Refl -> pure $ case a of 
  P.PInt bk n -> ask >>= \env -> pure 
    (MkSome . ETower $ ValE @(Value Z) @Int n ,TcGen env $ P.tokenPos bk ) 
  P.PDouble bk n -> ask >>= \env -> pure 
    (MkSome . ETower $ ValE @(Value F)  n ,TcGen env $ P.tokenPos bk) 
  P.PBool _ _ -> error "TODO"
  P.PVar bk s -> do 
    env <- ask 
    case M.lookup s $ varMapping  env of
      Just t -> case toSing  t of
        SomeSing @_ @t st -> withSingI st 
          $ pure (MkSome . ETower $ VarE (mkVar @t @ExprTag s) ,TcGen env $ P.tokenPos bk)
      Nothing -> 
        tell [SymbolNotDefined s $ P.tokenPos bk] >> empty
  P.PArray bk [] -> do 
    env <- ask
    SomeSing @_ @set set  <- case expectedType env of 
      Nothing -> error "TODO"
      Just t -> pure $ toSing t 
    withSingI set $ pure 
      ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
        $ (Empty :: Seq (ArrayE ErrorT ArithmeticT ArrayTag set))
      , TcGen env $ P.tokenPos bk)
  P.PArray bk (P.MkTupleArg _ e : xs) -> do 
    (MkSome @_ @e'  (ETower e'), _) <- typeCheck @ActionTag e 
    (MkSome @_ @xs' (ETower xs'), _) <- local (\env -> env{expectedType=Just (demote @e')}) 
      $ typeCheck @ActionTag (P.PArray bk xs)
    let e'' = ArrayInhE @ErrorT @ArithmeticT . ErrorT . ErrorInhE . ETower $ e'
    env <- ask
    case sing @xs' of 
      SArray sx -> withSingI sx $ case xs' of 
        ExpE (ErrorT (ErrorExpE (ArrayT (ArrayLiteralE @_ @_ @xs'' xs'')))) -> 
          case upcast @(ArrayE ErrorT ArithmeticT ArrayTag) @(Array xs'') @(Array e') upcastArrayT $ ArrayLiteralE xs'' of
            NonExistentUB -> error "TODO"
            SameTypeUB (ArrayLiteral (Dict,Dict) xs''') 
              -> pure 
                ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                  $ e'' :<| xs'''
                , TcGen env $ P.tokenPos bk
                ) 
            LeftUB  (ArrayLiteral (Dict,Dict) xs''') 
              -> ubIsCommutative @xs'' @e' $ case upcast @(ArrayE ErrorT ArithmeticT ArrayTag) @e' @xs'' upcastArrayT  e'' of
                SameTypeUB e''' -> pure 
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs'''
                  , TcGen env $ P.tokenPos bk
                  )
                LeftUB e''' 
                  -> pure 
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs''
                  , TcGen env $ P.tokenPos bk
                  )
                RightUB e''' -> pure 
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs''
                  , TcGen env $ P.tokenPos bk
                  )
                SomethingElseUB e'''  
                  -> pure
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs''
                  , TcGen env $ P.tokenPos bk
                  )

            RightUB (ArrayLiteral (Dict,Dict) xs''') 
              -> pure 
                ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                  $ e'' :<| xs'''
                , TcGen env $ P.tokenPos bk
                ) 
            SomethingElseUB  (ArrayLiteral (Dict,Dict) xs''') 
              -> ubIsCommutative @xs'' @e' $ case upcast @(ArrayE ErrorT ArithmeticT ArrayTag) @e' @xs'' upcastArrayT  e'' of
                SameTypeUB e''' -> pure 
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs''
                  , TcGen env $ P.tokenPos bk
                  )
                LeftUB e''' 
                  -> pure 
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs'''
                  , TcGen env $ P.tokenPos bk
                  )
                RightUB e''' -> pure 
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs'''
                  , TcGen env $ P.tokenPos bk
                  )
                SomethingElseUB e'''  
                  -> pure
                  ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayLiteralE 
                    $ e''' :<| xs'''
                  , TcGen env $ P.tokenPos bk
                  )
            _ -> error "impossible case"
        _ -> error "TODO"
      _ -> error "TODO"

  P.PParen _ e -> typeCheck @ActionTag e
  P.PDefer bk e -> do
    (MkSome @_ @e' (ETower e'),tcGen) <- typeCheck @ActionTag e
    withSingIRType @e'
      $ withRVType @(E Void2 ErrorT ExprTag) (sing @e')
      $ pure (MkSome . ETower $ DeferE e',tcGen{tcGenPos= P.tokenPos bk})

  P.PIf bk (e1,e2,e3) -> do
    env <- ask
    (MkSome @_ @x0 (ETower x0),e0r) <- typeCheck @ActionTag e1
    (MkSome @_ @x1 (ETower x1),e1r) <- typeCheck @ActionTag e2
    (MkSome @_ @x2 (ETower x2),e2r) <- typeCheck @ActionTag e3
    withSingIRType @x0 
      $ withSingIRType @x1
      $ withSingIRType @x2
      $ withRVType @(E Void2 ErrorT ExprTag) (sing @x0)
      $ withRVType @(E Void2 ErrorT ExprTag) (sing @x1)
      $ withRVType @(E Void2 ErrorT ExprTag) (sing @x2)
      $ case decideEquality (sing @(RValueT x0)) (sing @(Value Z)) of
        Nothing -> tell [TypeMismatch (ExpectedType $ Value Z)  (GotType $ demote @x0) $ tcGenPos e0r] >> empty
        Just Refl -> case upcastable @(RValueT x1) @(RValueT x2) @E @Void2 @ErrorT @ExprTag of
          NonExistentUB     ->  tell 
            [NonUnifiableTypes (demote @x1,tcGenPos e1r) (demote @x2,tcGenPos e2r) ] 
            >> empty
          SameTypeUB _      -> pure (MkSome . ETower $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)
          LeftUB _          -> pure (MkSome . ETower $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)
          RightUB _         -> pure (MkSome . ETower $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)
          SomethingElseUB _ -> pure (MkSome . ETower $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)


handlePrefixPrec :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handlePrefixPrec a = testEquality (sing @n) (sing @P.PrefixPrec) >>= \Refl -> pure $ case a of 
  P.PUMinus bk e -> typeCheckUOp @UMinusTag bk e (MkUOpEx ArithUMinusE) 
  P.OfHigherPrefixPrec x -> typeCheck @ActionTag x

handlePostfixPrec :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handlePostfixPrec a = testEquality (sing @n) (sing @P.PostfixPrec) >>= \Refl -> pure $ case a of 

  P.PApp bk f [] -> error "TODO" 

  P.PApp bk f [P.MkTupleArg _ arg ] -> do 
    MkSome @_ @g (ETower g) <- fst <$> typeCheck @ActionTag f 
    MkSome @_ @x (ETower x) <- fst <$> typeCheck @ActionTag arg
    withSingIRType @g 
      $ withSingIRType @x 
      $ case sing @(RValueT g) of 
        SValue ((:%->) @x' @ret x' ret) 
          -> withSingI x' 
          $ withSingI ret 
          $ withSingIUBType @(RValueT x) @x'
          $ case sing @(UpperBound (RValueT x) x') of 
            SJust x'' -> undefined 
        _ -> error "TODO"

  P.PApp bk f args -> undefined 
  P.PAppArr bk arr [] -> error "TODO"
  P.PAppArr bk arr [P.MkTupleArg _ i] -> do 
    MkSome @_ @xs xs <- fst <$> typeCheck @ActionTag arr
    MkSome @_ @ix ix <- fmap fst 
      $ local (\env -> env{expectedType=Just $ Value Z})
      $ typeCheck @ActionTag i  
    let 
      ix' = ArrayInhE @ErrorT @ArithmeticT . ErrorT . ErrorInhE $ ix
      xs' = ArrayInhE @ErrorT @ArithmeticT . ErrorT . ErrorInhE $ xs
      f :: ArrayE ErrorT ArithmeticT ArrayTag (Value Z) -> (AssocCtxMonad ArrayTag) Int
      f x = rvalue x >>= \case 
        ArrayInh (ErrorT (ErrorInh (ETower (Val (Dict,x',Dict)),_,_) ),_,_) -> pure x'
        _ -> error "TODO"

    env <- ask
    case (sing @xs, sing @ix) of 
      (SArray @sx sx, SValue SZ) -> withSingI sx $ pure 
        ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT $ 
          ArrayIndexE @ErrorT @ArithmeticT @sx f xs' ix'
        , TcGen env $ P.tokenPos bk
        )
      _ -> error "TODO"
  P.PAppArr bk arr (x:xs) -> typeCheck @ActionTag 
    $ flip (P.PAppArr bk) xs 
    $ P.PAppArr bk arr [x]

  P.OfHigherPostfixPrec x -> typeCheck @ActionTag x

handlePrec8 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handlePrec8 a = testEquality (sing @n) (sing @8) >>= \Refl -> pure $ case a of 
  P.PPower bk l r -> typeCheckBinOp @PowerTag bk l r (MkBinOpEx ArithPowerE)
  P.OfHigher8 x   -> typeCheck @ActionTag x 

handlePrec7 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handlePrec7 a = testEquality (sing @n) (sing @7) >>= \Refl -> pure $ case a of 
  P.PMul bk l r -> typeCheckBinOp @TimesTag bk l r (MkBinOpEx ArithTimesE)
  P.PDiv bk l r -> typeCheckBinOp @DivTag bk l r (MkBinOpEx ArithDivE)
  P.PMod bk l r -> typeCheckBinOp @ModTag bk l r (MkBinOpEx ArithModE)
  P.OfHigher7 x -> typeCheck @ActionTag x 

handlePrec6 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handlePrec6 a = testEquality (sing @n) (sing @6) >>= \Refl -> pure $ case a of 
  P.PPlus  bk l r -> typeCheckBinOp @PlusTag bk l r (MkBinOpEx ArithPlusE)
  P.PMinus bk l r -> typeCheckBinOp @MinusTag bk l r (MkBinOpEx ArithMinusE)
  P.OfHigher6 x -> typeCheck @ActionTag x


handlePrec1 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some ET, TcGen)) 
handlePrec1 a = testEquality (sing @n) (sing @1) >>= \Refl -> pure $ case a of 
  -- P.PLambda bk [P.MkTupleArg (Just t) bind] mReturnType pbody -> do
  --   env <- ask
  --   varName <- case P.yieldVarName bind of 
  --     Nothing -> throw $ FeatureNotImplemented "can only bind variables"
  --     Just v -> pure v 
  --   let env' = env{varMapping=M.insert varName (P.parserT2ZT t) $ varMapping env}
  --   (MkSome @_ @body' body',bodyE') <- local (const env') 
  --     $ typeCheck @ActionTag pbody
  --   (MkSome @_ @var  (Var _ var), _ ) <- local (const env') 
  --     $ typeCheck @ActionTag (P.PVar bk varName)
  --   case  P.parserT2ZT <$> mReturnType of 
  --     Nothing ->  withRVType @ExprTag (sing @body')
  --       $ pure (MkSome $ LambdaE var body', TcGen env $ P.tokenPos bk)
  --     Just returnType -> case toSing returnType of
  --       SomeSing @_ @returnType srt -> withSingI srt $ case upcast @_ @_ @returnType UpcastE body' of
  --         NonExistentUB -> throw $ NonUnifiableTypes (demote @returnType, P.tokenPos bk) (demote @body', tcGenPos bodyE')
  --         LeftUB {} -> throw $ ArgNotSubtype (demote @body', tcGenPos bodyE') returnType 
  --         SomethingElseUB {} -> throw $ ArgNotSubtype (demote @body', tcGenPos bodyE') returnType 
  --         SameTypeUB body ->  withRVType @ExprTag (sing @returnType)
  --           $ pure (MkSome $ LambdaE var body, TcGen env $ P.tokenPos bk)
  --         RightUB body ->  withRVType @ExprTag (sing @returnType)
  --           $ pure (MkSome  $ LambdaE var body, TcGen env $ P.tokenPos bk)
  --
  -- P.PLambda _ [] _ _ -> throw $ FeatureNotImplemented "Unbinded lambdas"
  --
  -- P.PLambda bk (P.MkTupleArg (Just t) bind : args) returnType body -> do
  --   env <- ask
  --   varName <- case P.yieldVarName bind of 
  --     Nothing -> error "can only bind variables"
  --     Just v -> pure v 
  --   let env' = env{varMapping= M.insert varName (P.parserT2ZT t) $ varMapping env}
  --   (MkSome @_ @lambda lambda,_) <- local (const env') 
  --     $ typeCheck @ActionTag (P.PLambda bk args returnType body)
  --   (MkSome @_ @var (Var _ var), _ ) <- local (const env') 
  --     $ typeCheck @ActionTag (P.PVar bk varName)
  --
  --   withRVType @ExprTag (sing @lambda)
  --     $ pure (MkSome $ LambdaE var lambda, TcGen env $ P.tokenPos bk)
  --
  -- P.PLambda _ (P.MkTupleArg Nothing _ : _) _ _ -> throw $ FeatureNotImplemented "Type Inference"
  P.OfHigher1 x -> typeCheck @ActionTag x 
  _ -> error "TODO"



data BinOpEx tag where 
  MkBinOpEx :: (forall l' r' c. 
    ( SingI (RValueT l')
    , SingI (RValueT r')
    , SingI (BinOpReturn tag (RValueT l') (RValueT r'))
    , BinOpReturn tag (RValueT l') (RValueT r') ~ RValueT c
    , BinOp tag (RValueT l') (RValueT r')
    , Biject ArrayT (RValueT l') 
    , Biject ArrayT (RValueT r') 
    , SingI l'
    , SingI r'
    , SingI c
    , Biject ArrayT (RValueT c)
    ) =>(Arithmetic ArrayT Void2 ArithmeticTag l' 
          -> Arithmetic ArrayT Void2 ArithmeticTag r'  
          -> Arithmetic ArrayT Void2 ArithmeticTag c
        ) 
    ) -> BinOpEx tag


data UOpEx tag where 
  MkUOpEx :: (forall a. 
    ( SingI a
    , Biject ArrayT (RValueT a)
    , Biject Void2 (RValueT a)
    , TypesCaseAnalysis (RValue (Arithmetic ArrayT Void2 ArithmeticTag))
    , ArithNumType (UOpReturn tag (RValueT a)) ~ ArithNumType (RValueT a)
    , UOp tag (RValueT a)
    ) => (Arithmetic ArrayT Void2 ArithmeticTag a 
          -> Arithmetic ArrayT Void2 ArithmeticTag a 
        ) 
    ) -> UOpEx tag

typeCheckUOp :: forall (tag :: ArithOpTags) n0.  
  ( SingI n0
  , SingI tag 
  )
  => P.BookeepInfo 
  -> P.EPrec n0 
  -> UOpEx tag  
  -> TCM (Some ET, TcGen)
typeCheckUOp bk l  (MkUOpEx f) = do 
    env <- ask 
    (MkSome @_ @l' l', _) <- typeCheck @ActionTag l 
    let l'' = ArithInhE @_ @Void2 . ArrayT . ArrayInhE . ErrorT . ErrorInhE $ l' 
    maybe (error "TODO") pure 
      $ join 
      $ withSingIRType @l'
      $ withBijectArrayT @(RValueT l')
      $ withUOp @tag @(RValueT l')
        ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayExpE . ArithmeticT  
          $ f @l' l''
        , TcGen env $ P.tokenPos bk 
        )  

typeCheckBinOp :: forall tag n0 n1.  
  ( SingI n0
  , SingI n1
  , SingI tag 
  )
  => P.BookeepInfo 
  -> P.EPrec n0
  -> P.EPrec n1 
  -> BinOpEx tag  
  -> TCM (Some ET, TcGen)
typeCheckBinOp bk l r (MkBinOpEx f) = do 
    env <- ask 
    (MkSome @_ @l' l', _) <- typeCheck @ActionTag l 
    (MkSome @_ @r' r', _) <- typeCheck @ActionTag r
    let l'' = ArithInhE @_ @Void2 . ArrayT . ArrayInhE . ErrorT . ErrorInhE $ l' 
        r'' = ArithInhE @_ @Void2 . ArrayT . ArrayInhE . ErrorT . ErrorInhE $ r'
    maybe (error "TODO") pure 
      $ join 
      $ join 
      $ join 
      $ join
      $ withSingIRType @l'
      $ withSingIRType @r'
      $ withSingIOpReturn @tag @(RValueT l') @(RValueT r')
      $ withBinOp @tag @(RValueT l') @(RValueT r')
      $ withBijectArrayT @(RValueT l')
      $ withBijectArrayT @(RValueT r')
      $ case lca @(BinOpReturn tag (RValueT l') (RValueT r')) of 
        MkLCA @_ @c c -> withSingI c $ withBijectArrayT @(RValueT c)  
            ( MkSome . ETower . ExpE . ErrorT . ErrorExpE . ArrayT . ArrayExpE . ArithmeticT  
              $ f @l' @r' @c   l'' r''
            , TcGen env $ P.tokenPos bk 
            )  
