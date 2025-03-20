
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ImpredicativeTypes         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneKindSignatures   #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE NoCUSKs                    #-}
{-# LANGUAGE NoNamedWildCards           #-}
{-# LANGUAGE NoStarIsType               #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ViewPatterns               #-}
module Zilly.Classic.TypeCheck2 where


import Parser.ClassicPlus.ZillyPlusParser qualified as P
import Utilities.LensM
import Utilities.TypedMap hiding (empty)
import Zilly.ADT.Expression
import Zilly.ADT.Action
import Zilly.Classic.Action
import Zilly.Classic.Expression
import Zilly.RValue
import Zilly.Types
import Zilly.Upcast
import Control.Monad.Reader


import Data.Kind (Type)
import Data.Singletons (SomeSing(..), SingI(..),SingKind(..),demote,withSingI)
import Control.Applicative (Alternative(..))
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.Writer.CPS
import Control.Monad.Trans.Maybe
import Text.Parsec (SourcePos)
import Data.Singletons.Decide hiding ((~>))
import Data.Type.Equality (testEquality)
import Data.Maybe (fromMaybe)
import qualified Data.Proof as Proof
import Data.Traversable
import Control.Monad (when)
import Debug.Trace (trace)

throw :: forall a e m f. (Alternative m, MonadWriter (f e) m,  Applicative f) => e -> m a
throw e = tell (pure e) >> empty

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
  | FeatureNotImplemented String
  | MalformedType String
  | CannotRedifined String 
instance Show TypeCheckErrors where
  show (SymbolNotDefined s pos) = "Symbol " <> show s <> " not defined " <> show pos
  -- show (FormulaNeedsLValue e pos) = "Needs lvalue " <> show e <> " " <> show pos 
  show (FormulaNeedsLValue _ pos) = "Needs lvalue at " <> show pos 
  show (TypeMismatch t1 t2 pos) = "Type mismatch between expected type: " <> show t1 <> " and actual type: " <> show t2 <> " at " <> show pos
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
  show (FeatureNotImplemented f) 
    = "The feature: "
    <> show f 
    <> " has not yet been implemented."
  show (MalformedType t) 
    = "MalformedType "
    <> show t
  show (CannotRedifined s)
    = "Impossible to redeclare symbol: "
    <> show s

newtype TCM a = TCM { unTCM :: ReaderT TypeCheckEnv (MaybeT (Writer ErrorLog) ) a }
  deriving newtype 
    ( Functor
    , Applicative
    , Monad
    , MonadReader TypeCheckEnv
    , MonadWriter ErrorLog
    , Alternative
    )

instance MonadFail TCM where 
  fail s = throw $ FeatureNotImplemented s

data TcGen  = TcGen
  { tcGenEnv :: TypeCheckEnv
  , tcGenPos :: SourcePos
  }




class TypeCheck actx e ret | e -> ret where
  type TCC actx ret :: ret -> Type
  type TCReturn actx e :: Type 
  typeCheck :: forall {f} {ctx}.
    ( AssocActionTag actx ~ ctx
    , TCC actx ret ~ f
    ) => e -> TCM (Some f,TCReturn actx e)

instance SingI n => TypeCheck ActionTag (P.EPrec n) Types where 
  type TCC ActionTag Types = E ExprTag 
  type TCReturn ActionTag  (P.EPrec n) = TcGen

  typeCheck a =  fromMaybe undefined 
    $   handleAtoms a 
    <|> handlePrefixPrec a
    <|> handlePostfixPrec a
    <|> handlePrec8 a
    <|> handlePrec7 a
    <|> handlePrec6 a
    <|> handlePrec4 a
    <|> handlePrec1 a
    <|> handlePrec0 a
 
instance  TypeCheck ActionTag P.A0 () where
  type TCC ActionTag () = Const' (A ActionTag '() )
  type TCReturn ActionTag P.A0 = TcGen 

  typeCheck (P.Decl t l r _) = handleAssign t l r
  typeCheck (P.Assign v e _) = handleReassign v e 
  typeCheck (P.Print e _)    = typeCheck @ActionTag e  >>= \(MkSome @_ @t e',env) -> case typesCaseAnalysisRV @ExprTag @t of
    Proof.Dict -> pure (MkSome . Const' @_ @'() . Print $ e', env)



newtype Const' a (b :: ()) = Const' {getConst' :: a}

data ExistLensM where 
  MkExistsLensM :: SingI a => LensM (AssocCtxMonad ActionTag) (E ExprTag a) -> ExistLensM 

handleAssign :: forall n' n e. 
  ( SingI n 
  , SingI e
  , SingI n'
  ) => P.TPrec n' -> P.EPrec n -> P.EPrec e -> TCM (Some (Const' (A ActionTag '())), TcGen)
handleAssign t a e
  | (Just Refl, P.PVar bk varName) <- (testEquality (sing @n) (sing @P.Atom),a) = do 
      env <- ask 
      (t', SomeSing @_ @var svar) <- case P.parserT2ZT t of 
        Nothing -> throw $ MalformedType $ P.showPTypes t
        Just t' -> pure (rLambdasArgs t',toSing $ rLambdasArgs t')
      when (varName `M.member` varMapping env) $ 
        throw (CannotRedifined varName)  
      let
        env' = env{varMapping= M.insert varName (rValueT t') $ varMapping env, expectedType=Just t'}
        var  = withSingI svar $ mkVar @var @ExprTag varName 
      (MkSome @_ @e' e', _) <- local (const env') $ typeCheck @ActionTag e
      withSingIRType @e'
        $ withSingI svar
        $ withSingIRType @var 
        $ withRV @ExprTag @e'
        $ withRV @ExprTag @var
        $ case upcastable @var @e'  @ExprTag of 
          SameTypeUB _ -> let co :: Const' (A ActionTag '() ) '() = Const' (var := e') in pure 
            ( MkSome co
            , TcGen env' $ P.tokenPos bk 
            )
          LeftUB _ -> let co :: Const' (A ActionTag '() ) '() = Const' (var := e') in pure 
            ( MkSome co
            , TcGen env' $ P.tokenPos bk 
            )
          RightUB _         -> throw $ RHSNotSubtype (demote @e', P.tokenPos bk) t'
          SomethingElseUB _ -> throw $ RHSNotSubtype (demote @e', P.tokenPos bk) t'
          NonExistentUB     -> throw $ RHSNotSubtype (demote @e', P.tokenPos bk) t'
  | (Just Refl, P.OfHigherPrefixPrec n) <- (testEquality (sing @n) (sing @P.PrefixPrec),a) = handleAssign t n e
  | (Just Refl, P.OfHigherPostfixPrec n) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = handleAssign t n e
  | (Just Refl, P.OfHigher8 n) <- (testEquality (sing @n) (sing @8),a) = handleAssign t n e
  | (Just Refl, P.OfHigher7 n) <- (testEquality (sing @n) (sing @7),a) = handleAssign t n e
  | (Just Refl, P.OfHigher6 n) <- (testEquality (sing @n) (sing @6),a) = handleAssign t n e
  | (Just Refl, P.OfHigher4 n) <- (testEquality (sing @n) (sing @4),a) = handleAssign t n e
  | (Just Refl, P.OfHigher1 n) <- (testEquality (sing @n) (sing @1),a) = handleAssign t n e
  | (Just Refl, P.OfHigher0 n) <- (testEquality (sing @n) (sing @0),a) = handleAssign t n e
  | otherwise = error "TODO"


handleReassign :: forall n e. 
  ( SingI n 
  , SingI e
  ) => P.EPrec n -> P.EPrec e -> TCM (Some (Const' (A ActionTag '())), TcGen)
handleReassign a e
  | (Just Refl, P.PVar bk varName) <- (testEquality (sing @n) (sing @P.Atom),a) = do 
      (MkSome @_ @var (VarE l), _) <- typeCheck @ActionTag (P.PVar bk varName )
      (MkSome @_ @e' e', _) <- local (\env -> env{expectedType= Just (demote @var) }) 
        $ typeCheck @ActionTag e
      env <- ask 
      let t' = demote @var
      withSingIRType @e'
        $ withSingIRType @var 
        $ withRV @ExprTag @var 
        $  withRV @ExprTag @e'
        $ case upcastable @var @(RValueT e')  @ExprTag of 
          SameTypeUB _ 
            -> let co :: Const' (A ActionTag '() ) '() = Const' (l :=. e') in pure 
              ( MkSome co
              , TcGen env $ P.tokenPos bk 
              )
          LeftUB _ 
            -> let co :: Const' (A ActionTag '() ) '() = Const' (l :=. e') in pure 
              ( MkSome co
              , TcGen env $ P.tokenPos bk 
              )
          RightUB _         -> throw $ RHSNotSubtype (demote @e', P.tokenPos bk) t'
          SomethingElseUB _ -> throw $ RHSNotSubtype (demote @e', P.tokenPos bk) t'
          NonExistentUB     -> throw $ RHSNotSubtype (demote @e', P.tokenPos bk) t'

  | (Just Refl, P.OfHigherPrefixPrec n) <- (testEquality (sing @n) (sing @P.PrefixPrec),a) = handleReassign n e
  | (Just Refl, P.OfHigherPostfixPrec n) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = handleReassign n e
  | (Just Refl, P.OfHigher8 n) <- (testEquality (sing @n) (sing @8),a) = handleReassign n e
  | (Just Refl, P.OfHigher7 n) <- (testEquality (sing @n) (sing @7),a) = handleReassign n e
  | (Just Refl, P.OfHigher6 n) <- (testEquality (sing @n) (sing @6),a) = handleReassign n e
  | (Just Refl, P.OfHigher4 n) <- (testEquality (sing @n) (sing @4),a) = handleReassign n e
  | (Just Refl, P.OfHigher1 n) <- (testEquality (sing @n) (sing @1),a) = handleReassign n e
  | (Just Refl, P.OfHigher0 n) <- (testEquality (sing @n) (sing @0),a) = handleReassign n e
  | (Just Refl, P.PAppArr bk arr []) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = case getVar arr of 
      Just varName -> handleReassign (P.PVar bk varName) e
      Nothing -> handleReassign arr e
  | (Just Refl, P.PAppArr bk (P.PAppArr _ arr xs) (y:ys)) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) 
      = handleReassign (P.PAppArr bk arr $ xs <> (y:ys)) e

  | (Just Refl, P.PAppArr {}) <- (testEquality (sing @n) (sing @P.PostfixPrec),a) = 
    throw $ FeatureNotImplemented "Arrays"
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

handleAtoms :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handleAtoms a = testEquality (sing @n) (sing @P.Inf) >>= \Refl -> pure $ case a of 
  P.PInt bk n -> ask >>= \env -> pure 
    (MkSome $ ValE n ,TcGen env $ P.tokenPos bk ) 
  P.PDouble {} ->  throw $ FeatureNotImplemented "Doubles"  
  P.PBool {} -> throw $ FeatureNotImplemented "Booleans"  
  P.PVar bk s -> do 
    env <- ask 
    case M.lookup s $ varMapping  env of
      Just t -> case toSing  t of
        SomeSing @_ @t st -> withSingI st 
          $ pure (MkSome  $ VarE (mkVar @t @ExprTag s) ,TcGen env $ P.tokenPos bk)
      Nothing -> 
        tell [SymbolNotDefined s $ P.tokenPos bk] >> empty
  P.PArray _ _ -> throw $ FeatureNotImplemented "Arrays"
  P.PParen _ e -> typeCheck @ActionTag e
  P.PDefer bk e -> do
    (MkSome @_ @e' e',tcGen) <- typeCheck @ActionTag e
    withSingIRType @e'
      $ withRVType @ExprTag (sing @e')
      $ pure (MkSome $ DeferE e',tcGen{tcGenPos= P.tokenPos bk})

  -- P.PFormula bk e -> do 
  --   (MkSome @_ @e' e',env) <- typeCheck @ActionTag e
  --   case e' of
  --     VarE v -> pure (MkSome $ FormulaE v,env)
  --     _ -> throw $ FormulaNeedsLValue (P.OfHigher0 $ P.PParen bk e) $ P.tokenPos bk

  P.PIf bk (e1,e2,e3) -> do
    env <- ask
    (MkSome @_ @x0 x0,e0r) <- typeCheck @ActionTag e1
    (MkSome @_ @x1 x1,e1r) <- typeCheck @ActionTag e2
    (MkSome @_ @x2 x2,e2r) <- typeCheck @ActionTag e3
    withSingIRType @x0 
      $ withSingIRType @x1
      $ withSingIRType @x2
      $ withRVType @ExprTag (sing @x0)
      $ withRVType @ExprTag (sing @x1)
      $ withRVType @ExprTag (sing @x2)
      $ case decideEquality (sing @(RValueT x0)) (sing @(Value Z)) of
        Nothing -> tell [TypeMismatch (ExpectedType $ Value Z)  (GotType $ demote @x0) $ tcGenPos e0r] >> empty
        Just Refl -> case upcastable @(RValueT x1) @(RValueT x2) @ExprTag of
          NonExistentUB     ->  tell 
            [NonUnifiableTypes (demote @x1,tcGenPos e1r) (demote @x2,tcGenPos e2r) ] 
            >> empty
          SameTypeUB _      -> pure (MkSome $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)
          LeftUB _          -> pure (MkSome $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)
          RightUB _         -> pure (MkSome $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)
          SomethingElseUB _ -> pure (MkSome $ IfE x0 x1 x2,TcGen env $ P.tokenPos bk)

handlePrefixPrec :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrefixPrec a = testEquality (sing @n) (sing @P.PrefixPrec) >>= \Refl -> pure $ case a of 
  P.PUMinus bk e -> typeCheck @ActionTag (P.PMinus bk (P.OfHigher6 $ P.PInt bk 0) e)
  P.OfHigherPrefixPrec x -> typeCheck @ActionTag x

handlePostfixPrec :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePostfixPrec a = testEquality (sing @n) (sing @P.PostfixPrec) >>= \Refl -> pure $ case a of 

  P.PApp _ _ [] -> throw $ FeatureNotImplemented "Unbinded Lambdas" 
  P.PApp bk f [P.MkTupleArg _ arg] 
    | Just (P.PVar bk' "formula") <- P.normalizeEPrec' @P.Atom f
    , Just var@(P.PVar {})        <- P.normalizeEPrec' @P.Atom arg -> do 
      env <- ask 
      MkSome @_ @x (VarE var') <- fst <$> typeCheck @ActionTag var 
      pure (MkSome $ FormulaE var' , TcGen env $ P.tokenPos bk)
    | Just (P.PVar bk' "formula") <- P.normalizeEPrec' @P.Atom f -> throw $ FeatureNotImplemented "formula of non LValued argument" 
  P.PApp bk f [P.MkTupleArg _ arg ] -> do 
    env <- ask
    MkSome @_ @g g <- fst <$> typeCheck @ActionTag f 
    MkSome @_ @x x <- fst <$> typeCheck @ActionTag arg
    withSingIRType @g 
      $ withSingIRType @x
      $ withRV @ExprTag @g
      $ withRV @ExprTag @x
      $ case sing @(RValueT g) of 
        SValue ((:%->) @x' @ret x' ret) 
          -> withSingI x' 
          $ withSingI ret 
          $ withSingIUBType @(RValueT x) @x'
          $ withSingIUBType @x' @(RValueT x)
          $ case upcastable @x' @(RValueT x)  @ExprTag of 
            NonExistentUB -> throw $ ArgNotSubtype (demote @x,P.tokenPos bk) (demote @x') 
            LeftUB _      -> ubIsCommutative @x' @(RValueT x) $ pure (MkSome $ AppE g x, TcGen env $ P.tokenPos bk)
            SomethingElseUB _ -> throw $ ArgNotSubtype (demote @x,P.tokenPos bk) (demote @x') 
            SameTypeUB _ -> pure (MkSome $ AppE g x, TcGen env $ P.tokenPos bk)
            RightUB _    -> throw $ ArgNotSubtype (demote @x,P.tokenPos bk) (demote @x') 

        _ -> throw $ AppNotAFun (demote @g) $ P.tokenPos bk

  P.PApp bk f (x:xs) -> typeCheck @ActionTag (P.PApp bk (P.PApp bk f [x]) xs)
  P.PAppArr {}  -> throw $ FeatureNotImplemented "Arrays"
  P.OfHigherPostfixPrec x -> typeCheck @ActionTag x

handlePrec8 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrec8 a = testEquality (sing @n) (sing @8) >>= \Refl -> pure $ case a of 
  P.PPower {} -> throw $ FeatureNotImplemented "Power notation" 
  P.OfHigher8 x   -> typeCheck @ActionTag x 

handlePrec7 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrec7 a = testEquality (sing @n) (sing @7) >>= \Refl -> pure $ case a of 
  P.PMul bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @r') (sing @(Value Z)) ) of
        (Just Refl, Just Refl) -> pure 
          ( MkSome $ (VarE @(Value Z ~> Value Z ~> Value Z) "mul" ) $$ l' $$ r'
          , TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)


  P.PDiv {} -> throw $ FeatureNotImplemented "Division notation" 
  P.PMod {} -> throw $ FeatureNotImplemented "Modulo notation" 
  P.OfHigher7 x -> typeCheck @ActionTag x 

handlePrec6 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrec6 a = testEquality (sing @n) (sing @6) >>= \Refl -> pure $ case a of 
  P.PPlus  bk l r -> typeCheck @ActionTag (P.PMinus bk l $ P.PParen bk $ P.PMinus bk (P.OfHigher6 $ P.PInt bk 0) r)
  P.PMinus bk l r -> do 
    env <- ask
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of
        (Just Refl, Just Refl) -> pure (MkSome $ MinusE l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)

  P.OfHigher6 x -> typeCheck @ActionTag x

handlePrec4 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrec4 a = testEquality (sing @n) (sing @4) >>= \Refl -> pure $ case a of 
  P.PLT bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of
        (Just Refl, Just Refl) -> pure (MkSome $ LessE l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)
  P.PLTEQ bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r    
    let res a b =
          (VarE @(Value Z ~> Value Z ~> Value Z) "lteq")
            $$ a
            $$ b
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of
        (Just Refl, Just Refl) -> pure (MkSome $ res l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)
  P.PGT bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    let res a b =
          (VarE @(Value Z ~> Value Z ~> Value Z) "gt")
            $$ a
            $$ b
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of
        (Just Refl, Just Refl) -> pure (MkSome $ res l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)  
  P.PGTEQ bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    let res a b =
          (VarE @(Value Z ~> Value Z ~> Value Z) "gteq")
            $$ a
            $$ b
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of

        (Just Refl, Just Refl) -> pure (MkSome $ res l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)
  P.PEQ bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    let res a b =
          (VarE @(Value Z ~> Value Z ~> Value Z) "eq")
            $$ a
            $$ b
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of

        (Just Refl, Just Refl) -> pure (MkSome $ res l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)  
  P.PNEQ bk l r -> do 
    env <- ask 
    MkSome @_ @l' l' <- fst <$> typeCheck @ActionTag l
    MkSome @_ @r' r' <- fst <$> typeCheck @ActionTag r
    let res a b =
          (VarE @(Value Z ~> Value Z ~> Value Z) "neq")
            $$ a
            $$ b
    withSingIRType @l'
      $ withSingIRType @r'
      $ withRVType @ExprTag (sing @l')
      $ withRVType @ExprTag (sing @r')
      $ case (decideEquality (sing @l') (sing @(Value Z)), decideEquality (sing @(RValueT r')) (sing @(Value Z)) ) of
        (Just Refl, Just Refl) -> pure (MkSome $ res l' r',TcGen env $ P.tokenPos bk)
        (Nothing,_) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @l') (P.tokenPos bk)
        (_,Nothing) -> throw  $ TypeMismatch (ExpectedType $ Value Z) (GotType $ demote @r') (P.tokenPos bk)
  P.OfHigher4 x -> typeCheck @ActionTag x 
 

handlePrec1 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrec1 a = testEquality (sing @n) (sing @1) >>= \Refl -> pure $ case a of 
  P.PLambda bk [P.MkTupleArg (Just t) bind] mReturnType pbody -> do
    env <- ask
    varName <- case P.yieldVarName bind of 
      Nothing -> throw $ FeatureNotImplemented "can only bind variables"
      Just v -> pure v 
    (t', SomeSing @_ @var svar) <- case P.parserT2ZT t of 
      Nothing -> throw $ MalformedType $ P.showPTypes t
      Just t' -> pure (t',toSing t')

    let 
      env'  = env{varMapping=M.insert varName (rValueT t') $ varMapping env}
      var   = withSingI svar $ mkVar @var @ExprTag varName 
      var'  = withSingI svar $ withSingIRType @var $  mkVar @(RValueT var) @ExprTag varName 

    (MkSome @_ @body' body',bodyE') <- local (const env') 
      $ typeCheck @ActionTag pbody

    withSingI svar $ withSingIRType @var $ case  mReturnType >>= P.parserT2ZT of 
      Nothing ->  withRVType @ExprTag (sing @body')
        $ pure (MkSome $ LambdaE var' body', TcGen env $ P.tokenPos bk)
      Just returnType -> case toSing returnType of
        SomeSing @_ @returnType srt -> withSingI srt $ case upcast @_ @_ @returnType UpcastE body' of
          NonExistentUB -> throw $ NonUnifiableTypes (demote @returnType, P.tokenPos bk) (demote @body', tcGenPos bodyE')
          LeftUB {} -> throw $ ArgNotSubtype (demote @body', tcGenPos bodyE') returnType 
          SomethingElseUB {} -> throw $ ArgNotSubtype (demote @body', tcGenPos bodyE') returnType 
          SameTypeUB body ->  withRVType @ExprTag (sing @returnType)
            $ pure (MkSome $ LambdaE var body, TcGen env $ P.tokenPos bk)
          RightUB body ->  withRVType @ExprTag (sing @returnType)
            $ pure (MkSome  $ LambdaE var body, TcGen env $ P.tokenPos bk)

  P.PLambda _ [] _ _ -> throw $ FeatureNotImplemented "Unbinded lambdas"

  P.PLambda bk (P.MkTupleArg (Just t) bind : args) returnType body -> do
    env <- ask
    varName <- case P.yieldVarName bind of 
      Nothing -> throw $ FeatureNotImplemented "Non variable binding"
      Just v -> pure v
    (t', SomeSing @_ @var svar) <- case P.parserT2ZT t of 
      Nothing -> throw $ MalformedType $ P.showPTypes t
      Just t' -> pure (t',toSing t')

    let 
      env' = env{varMapping=M.insert varName (rValueT t') $ varMapping env}
      var  = withSingI svar $ mkVar @var @ExprTag varName 

    (MkSome @_ @lambda lambda,_) <- local (const env') 
      $ typeCheck @ActionTag (P.PLambda bk args returnType body)
    withSingI svar 
      $ withRVType @ExprTag (sing @lambda)
      $ pure (MkSome $ LambdaE var lambda, TcGen env $ P.tokenPos bk)

  P.PLambda _ (P.MkTupleArg Nothing _ : _) _ _ -> throw $ FeatureNotImplemented "Type Inference"
  P.OfHigher1 x -> typeCheck @ActionTag x 

handlePrec0 :: forall n. SingI n => P.EPrec n ->  Maybe (TCM (Some (E ExprTag), TcGen)) 
handlePrec0 a = testEquality (sing @n) (sing @0) >>= \Refl -> pure $ case a of 
  P.OfHigher0 x -> typeCheck @ActionTag x 


typeCheckProgram :: Map Symbol Types -> P.A1 -> TCM (Map Symbol Types,[A ActionTag '()])
typeCheckProgram ienv as = forAccumM ienv (f as) $ \env a -> do
  (MkSome @_ @a' a',r) <- local (const $ TCE env Nothing) $  typeCheck @ActionTag @_ @() a
  pure (varMapping $ tcGenEnv r,getConst' a')
  
  where 
    f (P.OfA0 a) = [a]
    f (P.Seq x xs) = x : xs

typeCheckProgram' :: Map Symbol Types -> P.A1 ->  (Map Symbol Types, Maybe [A ActionTag '()],ErrorLog)
typeCheckProgram' gamma as = case runWriter . runMaybeT . runReaderT (unTCM $ typeCheckProgram gamma as) $ TCE gamma Nothing of
  (Just (gamma',as'),elog) -> (gamma',Just as',elog)
  (Nothing,elog)           -> (gamma,Nothing,elog)
