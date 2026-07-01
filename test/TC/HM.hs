{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module TC.HM where

import Zilly.Puzzle.Types.Exports qualified as T
import Zilly.Puzzle.Parser
import Zilly.Puzzle.TypeCheck.Unsugar
import Zilly.Puzzle.TypeCheck.HM
import Control.Monad.RWS
import Control.Monad.Except
import Control.Exception
import Control.Applicative (Alternative)
import Zilly.Puzzle.Action.Classes
import Data.Map (Map, (!), (!?))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text qualified as Text
import Data.String (IsString(..))
import Prelude.Singletons hiding (Map)
import GHC.TypeLits.Singletons
import Control.Monad.State.Strict
import Test.QuickCheck
import Debug.Trace (trace)
import Data.List qualified as List
import Control.Concurrent

data HMStage

$(genCtxInstances ''HMStage ''PTInfo)

ctxGenerator :: IO (MVar T.Types, BookeepInfo)
ctxGenerator = (,undefined) <$> newEmptyMVar

data HMTestState = HMTestState
  { typeVarCounter :: !Int
  , constraints :: [Constraint]
  , typeEnv :: Map String [(String,[T.Types])]
  , consEnv :: Map String (T.Types, [T.Types])
  }

data HMTestReader = HMTestReader
  { gammaEnv :: !Gamma

  }

data HMTestWriter = HMTestWriter
  { tcErrorLog :: [String]
  }

instance Semigroup HMTestWriter where
  (HMTestWriter e1) <> (HMTestWriter e2) = HMTestWriter (e1 <> e2)

instance Monoid HMTestWriter where
  mempty = HMTestWriter mempty

newtype HMTestM a = HMTestM
  { runHMTestM' :: ExceptT String (RWST HMTestReader HMTestWriter HMTestState IO) a
  } deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadIO
    , Alternative
    , MonadReader HMTestReader
    , MonadWriter HMTestWriter
    , MonadState HMTestState
    )

runHMTestM
  :: HMTestState
  -> HMTestReader
  -> HMTestM a
  -> IO (Either String a, HMTestState, HMTestWriter)
runHMTestM s r  (HMTestM m) = runRWST (runExceptT m) r s

instance MonadError String HMTestM where
  throwError = HMTestM . throwError
  catchError (HMTestM m) h = HMTestM (catchError m (runHMTestM' . h))

instance MonadFail HMTestM where
  fail = throwError

instance HasTypeEnv HMTestM where
  declareType _ _ = pure ()
  updateType _ _ = pure ()
  lookupType n = gets (M.lookup n . typeEnv)
  lookupCons n = gets (M.lookup n . consEnv)

instance InferMonad HMTestM where
  fresh = do
    s <- get
    let n = typeVarCounter s
    put s { typeVarCounter = n + 1 }
    return $ T.TVar (T.TV (Text.pack ("'a" ++ show n)))
  constraint c = modify (\s -> s { constraints = c : constraints s })
  gamma = asks gammaEnv
  getConstraints = gets constraints
  reportTCError err = tell (HMTestWriter [err])
  throwIrrecoverableError = throwError
  withVar n t = local (\r -> r { gammaEnv = M.insert (T.TV $ fromString n) t (gammaEnv r) })




data UntypedBoolExpr = BoolExpr
  { getUBE :: EPrec HMStage 0
  , ubeFreeVars :: Set String
  }

newtype UBEMonad a = UBEMonad
  { runUBEMonad :: State Int a
  } deriving newtype
    ( Functor
    , Applicative
    , Monad
    , MonadState Int
    )


newtype VarGen = VarGen { getVarGen :: String }

instance Arbitrary VarGen where
  arbitrary = do
    n <- choose (1,3)
    chars <- vectorOf n (elements ['a'..'z'])
    pure $ VarGen chars

instance Arbitrary UntypedBoolExpr where
  arbitrary = undefined

-- tcBoolFirstOrder :: HMTestState -> (Set String -> HMTestReader) -> Property
-- tcBoolFirstOrder initialState initialReader = forAllShow (arbitrary @UntypedBoolExpr) show' prop
--   where
--     show' :: UntypedBoolExpr -> String
--     show' (BoolExpr e _) = show e
--
--     prop (BoolExpr e fvs) = ioProperty $ do
--       let run = do
--             -- liftIO $ putStrLn $ "expression: " <> show e
--             te  <- infer e
--             -- liftIO $ putStrLn $ "type before solving: " <> show te
--             cs <- gets constraints
--             -- liftIO $ putStrLn $ "constraints: " <> show cs
--             substs <- solve emptySubst cs
--             -- liftIO $ putStrLn $ "substitutions: " <> show substs
--             let tes = apply substs te
--             -- liftIO $ putStrLn $ "type after solving: " <> show tes
--             pure (te,tes,cs,substs)
--       (res, finalState, log) <- runHMTestM initialState (initialReader fvs) run
--       case res of
--         Left err -> pure . flip counterexample False
--           $ "Type error: "
--           <> err
--           <> "\nLog:\n"
--           <> unlines (tcErrorLog log)
--         Right (te,tes,cs,substs)  -> do
--           liftIO . putStrLn
--             $ "Expression: \n"
--             <> show e
--             <> "\nInferred type: "
--             <> show tes
--             <> "\nType before substitutions: "
--             <> show te
--             <>  "\nConstraints: "
--             <> show cs
--             <> "\nSubstitutions: "
--             <> show substs
--             <> "\nLog:\n"
--             <> unlines (tcErrorLog log)
--           pure $ property True
--
--

props :: [Property]
props =
  [ label "Typechecking fn('a x) -> x"
    $ once $ identityTyping
  , label "TypeChecking fn(lazy<'a> x) -> x"
    $ once $ identityTyping2
  , label "TypeChecking fn('x x) -> fn('y y) -> x = y"
    $ once $ eqTypingGen
  , label "TypeChecking fn(('a -> 'b) f) -> fn('a x) -> f(x)"
    $ once $ higherOrderTyping

  , label ("Checking empty array gets polymorphic type")
    $ once $ emptyArrayCheck
  , label ("Checking that a monovector array gets correct type (unconstrained dimension)")
    $ once $ monovectorArrayCheck
  , label ("Checking that a monovector array gets correct type (constrained dimension)")
    $ once $ monovectorArrayCheck'
  , label ("Checking that a poly/bounded vector array gets correct type")
    $ once $ boundedVectorArrayCheck
  , label ("Check if rigid type vars work")
    $ once $ constRigidCheck
  -- , label "Type check boolean expressions (first-order)"
  --   $ tcBoolFirstOrder initialState initialReader
  -- , label "Type check boolean expressions (first-order, no bindings)"
  --   $ tcBoolFirstOrder initialState noBindingsReader
  ]
  where
  initialState = HMTestState
    { typeVarCounter = 0
    , constraints = []
    , typeEnv = M.fromList
        [
        ]
    , consEnv = M.fromList
        [
        ]
    }
  initialReader = \fvs -> HMTestReader
    { gammaEnv =  M.fromList [(T.TV (fromString v), Forall S.empty T.ZBool) | v <- S.toList fvs]
    }
  noBindingsReader = \_ -> HMTestReader { gammaEnv = mempty }


-----------------
-- Unit Tests
-----------------


genericBuilder :: EPrec TCTag 0 -> (T.Types -> Property) -> Property
genericBuilder expr prop = ioProperty $ do
  let run = do
        te  <- infer expr
        cs <- gets constraints
        substs <- solve emptySubst cs
        let !tes = apply substs te
        pure (te,tes,cs,substs)
  (res, finalState, log) <- runHMTestM initialState (initialReader (S.singleton "x")) run
  case res of
    Left err -> pure . flip counterexample False
      $ "Type error: "
      <> err
      <> "\nLog:\n"
      <> unlines (tcErrorLog log)
    Right (te,tes,cs,substs)  -> do
      liftIO . putStrLn
        $ "Expression: \n"
        <> show expr
        <> "\nInferred type:\n"
        <> show tes
        <> "\nType before substitutions:\n"
        <> show te
        <>  "\nConstraints:\n"
        <> unlines (show <$> cs)
        <> "\nSubstitutions: "
        <> (\(Subst s)-> List.intercalate ", " [ Text.unpack v <> " |-> " <> show t | (T.TV v,t) <- M.toList s ])substs
        <> "\nLog:\n"
        <> unlines (tcErrorLog log)
      pure $ prop tes
  where
  initialState = HMTestState
    { typeVarCounter = 0
    , constraints = []
    , typeEnv = M.fromList
        [
        ]
    , consEnv = M.fromList
        [
        ]
    }
  initialReader = \fvs -> HMTestReader
    { gammaEnv =  M.fromList [(T.TV (fromString v), Forall S.empty T.ZBool) | v <- S.toList fvs]
    }



identityTyping :: Property
identityTyping = ioProperty $ do
  lctx <- ctxGenerator
  xCtx <- ctxGenerator
  xBodyCtx <- ctxGenerator
  let expr = OfHigher0
            $ PLambda @TCTag lctx
              [ (OfHigher0 $ PVar @TCTag xCtx "x", "'a") ]
              Nothing
              (OfHigher1 $ PVar @TCTag xBodyCtx "x")

  pure $ genericBuilder expr (property . checkIdType)
  where
  checkIdType :: T.Types -> Bool
  checkIdType (a T.:-> T.RV b) = a == b
  checkIdType _ = False

identityTyping2 :: Property
identityTyping2 = ioProperty $ do
  lctx <- ctxGenerator
  xCtx <- ctxGenerator
  xBodyCtx <- ctxGenerator

  let expr = OfHigher0
            $ PLambda @TCTag lctx
              [ (OfHigher0 $ PVar @TCTag xCtx "x", T.Lazy "'a") ]
              Nothing
              (OfHigher1 $ PVar @TCTag xBodyCtx "x")

  pure $ genericBuilder expr (property . checkIdType)
  where
  checkIdType :: T.Types -> Bool
  checkIdType (a T.:-> b) = T.rtype a == b
  checkIdType _ = False

eqTypingGen :: Property
eqTypingGen = ioProperty $ do
  lctx1 <- ctxGenerator
  xCtx  <- ctxGenerator
  lctx2 <- ctxGenerator
  yCtx  <- ctxGenerator
  xBodyCtx <- ctxGenerator
  yBodyCtx <- ctxGenerator
  eqCtx <- ctxGenerator
  let expr = OfHigher0
          $ PLambda @TCTag lctx1
            [ (OfHigher0 $ PVar @TCTag xCtx "x", "'x")
            ]
            Nothing
            $ PLambda @TCTag lctx2
              [ (OfHigher0 $ PVar @TCTag yCtx "y", "'y")
              ]
              Nothing
              (OfHigher1
                $ PEQ @Atom @TCTag eqCtx
                  (PVar @TCTag xBodyCtx "x")
                  (PVar @TCTag yBodyCtx "y")
              )

  pure $ genericBuilder expr (property . checkEqType)
  where
  checkEqType :: T.Types -> Bool
  checkEqType (T.TConstraints cs (a T.:-> b T.:-> c)) = and
    [ a == b
    , S.member ("Eq", c, []) cs
    ]
  checkEqType _ = False

higherOrderTyping :: Property
higherOrderTyping = ioProperty $ do
  lctx1 <- ctxGenerator
  fCtx  <- ctxGenerator
  lctx2 <- ctxGenerator
  xCtx  <- ctxGenerator
  pAppCtx <- ctxGenerator
  fBodyCtx <- ctxGenerator
  xBodyCtx <- ctxGenerator

  let expr = OfHigher0
        $ PLambda @TCTag lctx1
          [ (OfHigher0 $ PVar @TCTag fCtx "f", "'a" T.:-> "'b")
          ]
          Nothing
          $ PLambda @TCTag lctx2
            [ (OfHigher0 $ PVar @TCTag xCtx "x", "'c")
            ]
            Nothing
          (OfHigher1
            $ PApp @TCTag pAppCtx
              (OfHigherPostfixPrec $ PVar @TCTag fBodyCtx "f")
              [OfHigher0 $ PVar @TCTag xBodyCtx "x"]
          )

  pure $ genericBuilder expr (property . checkHOType)
  where
  checkHOType :: T.Types -> Bool
  checkHOType t = t == "'b"
  checkHOType _ = False

constRigidCheck :: Property
constRigidCheck = ioProperty $ do
  clctx1 <- ctxGenerator
  cXtx  <- ctxGenerator
  clctx2 <- ctxGenerator
  cYtx  <- ctxGenerator
  cXBodyCtx <- ctxGenerator
  argCtx <- ctxGenerator
  app1Ctx <- ctxGenerator
  parenCtx <- ctxGenerator
  app2Ctx <- ctxGenerator
  paren2Ctx <- ctxGenerator
  arg2Ctx <- ctxGenerator
  let c = PLambda @TCTag clctx1
        [ (OfHigher0 $ PVar @TCTag cXtx "x", T.TVar (T.TV "'a"))
        ]
        Nothing
        $ PLambda @TCTag clctx2
          [ (OfHigher0 $ PVar @TCTag cYtx "y", T.TVar $ T.TV "'a")
          ]
          Nothing
        (OfHigher1 $ PVar @TCTag cXBodyCtx "x")
      arg = OfHigher0 $ PInt @TCTag argCtx 5
      app1 = OfHigher0 $ PApp @TCTag app1Ctx
        (OfHigherPostfixPrec $ PParen @1 @TCTag parenCtx  c)
        [arg]
      app2 = OfHigher0 $ PApp @TCTag app2Ctx
        (OfHigherPostfixPrec $ PParen @_ @TCTag paren2Ctx  app1)
        [OfHigher0 $ PString @TCTag arg2Ctx "bad argument"]
        -- [OfHigher0 $ PInt @TCTag arg2Ctx 10]

      expr = app2 -- app2

  pure $ genericBuilder expr (property . checkConstType)
  where
  checkConstType :: T.Types -> Bool
  checkConstType t = t == T.Z
  checkConstType _ = False

emptyArrayCheck :: Property
emptyArrayCheck = ioProperty $ do
  ctx <- ctxGenerator
  let expr = OfHigher0 $ PArray @0 @TCTag ctx []
  pure $ genericBuilder expr (property . checkEmptyArrayType)
  where
  checkEmptyArrayType :: T.Types -> Bool
  checkEmptyArrayType (T.TCon "array" [_,T.TVar _]) = True
  checkEmptyArrayType _ = False

monovectorArrayCheck :: Property
monovectorArrayCheck = ioProperty $ do
  arrCtx <- ctxGenerator
  e1Ctx <- ctxGenerator
  e2Ctx <- ctxGenerator
  e3Ctx <- ctxGenerator
  let expr = OfHigher0 $ PArray @0 @TCTag arrCtx
        [ OfHigher0 $ PInt @TCTag e1Ctx 1
        , OfHigher0 $ PInt @TCTag e2Ctx 2
        , OfHigher0 $ PInt @TCTag e3Ctx 3
        ]

  pure $ genericBuilder expr (property . checkVectorArrayType)
  where
  checkVectorArrayType :: T.Types -> Bool
  checkVectorArrayType (T.TCon "array" [_, T.Z]) = True
  checkVectorArrayType _ = False

monovectorArrayCheck' :: Property
monovectorArrayCheck' = ioProperty $ do
  flctx <- ctxGenerator
  fxCtx <- ctxGenerator
  fXBodyCtx <- ctxGenerator
  arrCtx <- ctxGenerator
  e1Ctx <- ctxGenerator
  e2Ctx <- ctxGenerator
  e3Ctx <- ctxGenerator
  appCtx <- ctxGenerator
  parenCtx <- ctxGenerator
  let f    = PLambda @TCTag flctx
        [ (OfHigher0 $ PVar @TCTag fxCtx "x", T.NDArray 1 T.Z)
        ]
        Nothing
        (OfHigher1 $ PVar @TCTag fXBodyCtx "x")

      arr = PArray @0 @TCTag arrCtx
        [ OfHigher0 $ PInt @TCTag e1Ctx 1
        , OfHigher0 $ PInt @TCTag e2Ctx 2
        , OfHigher0 $ PInt @TCTag e3Ctx 3
        ]
      farr = OfHigher0 $ PApp @TCTag appCtx
        (OfHigherPostfixPrec $ PParen @1 @TCTag parenCtx f)
        [OfHigher0 arr]
      expr = farr

  pure $ genericBuilder expr (property . checkVectorArrayType)
  where
  checkVectorArrayType :: T.Types -> Bool
  checkVectorArrayType (T.TConstraints _ (T.NDArray 1 T.Z)) = True
  checkVectorArrayType _ = False

boundedVectorArrayCheck :: Property
boundedVectorArrayCheck = ioProperty $ do
  arrCtx <- ctxGenerator
  e1Ctx <- ctxGenerator
  e2Ctx <- ctxGenerator
  e3Ctx <- ctxGenerator

  let expr = OfHigher0 $ PArray @0 @TCTag arrCtx
        [ OfHigher0 $ PInt @TCTag e1Ctx 1
        , OfHigher0 $ PFloat @TCTag e2Ctx 2.5
        , OfHigher0 $ PInt @TCTag e3Ctx 3
        ]

  pure $ genericBuilder expr (property . checkVectorArrayType)
  where
  checkVectorArrayType :: T.Types -> Bool
  checkVectorArrayType (T.TConstraints _ (T.TCon "array" [_, T.F])) = True
  checkVectorArrayType _ = False
