{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
module Main where

-- import Zilly.Classic.Runner
import GHC.Wasm.Prim
import Language.Javascript.JSaddle.Wasm qualified as JSaddle.Wasm
import Zilly.Runner (buildUniversalInterpreter)
import GHC.IO

main :: IO ()
main = pure ()

type InterpreterSig a = (a -> IO a)

foreign import javascript "wrapper"
  wrapper :: InterpreterSig JSString -> IO JSVal

foreign export  javascript cmain :: IO JSVal

cmain :: IO JSVal
cmain = do
  f <- buildUniversalInterpreter
  wrapper $ \js -> toJSString <$> f (fromJSString js)






