{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
module Main where

-- import Zilly.Classic.Runner
import GHC.Wasm.Prim
import Language.Javascript.JSaddle.Wasm qualified as JSaddle.Wasm
import Zilly.Classic.Runner (buildInterpreter')
import GHC.IO

main :: IO ()
main = pure ()

type InterpreterSig a = (a -> IO a)

foreign import javascript "wrapper"
  wrapper :: InterpreterSig JSString -> IO JSVal

foreign export  javascript cmain :: IO JSVal

cmain :: IO JSVal
cmain = do
  f <- buildInterpreter' 
  wrapper $ \js -> toJSString <$> f (fromJSString js)






