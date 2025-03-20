{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Parser.ParserZ where

{-
Based on 

Design Patterns for Parser Combinators (Functional Pearl)

ACM ISBN 978-1-4503-8615-9/21/08.
https://doi.org/10.1145/3471874.3472984
-}

import Text.Parsec hiding (token)
import Text.Parsec.String
import Text.Parsec.Combinator
import Data.String (IsString(..))
import Control.Monad
import Control.Applicative ((<**>))
import Data.Functor.Const
import Data.Functor
import Data.Functor.Identity
import Parser.Utilities

newtype Channel = Channel Int deriving newtype (Eq, Show)
newtype Seq     = Seq Int deriving newtype (Eq, Show)
data Tab = Tab deriving Eq
newtype Payload' a  = Payload a deriving newtype (Eq, Show)
type Payload = Payload' String
data EOT = EOT deriving Eq

instance Show Tab where show _ = "\t"
instance Show EOT where show _ = "\EOT"

data Packet' a = Packet Channel Seq Tab (Payload' a) EOT
  deriving Eq

type Packet = Packet' String

bracketS :: String -> String
bracketS s = "<" <> s <> ">"

emphS :: String -> String
emphS s = "[" <> s <> "]"

serializePacket :: Packet -> String
serializePacket (Packet c s t m eot) = concat
  [ show c
  , emphS $ show s
  , show t
  , show m
  , show eot
  ]

pChannel :: Parser Channel
pChannel = Channel <$> number

pSeq :: Parser Seq 
pSeq = Seq <$> number

pTab :: Parser Tab
pTab = Tab <$ char '\t' <|> Tab <$ spaces <|> pure Tab

pEOT :: Parser EOT
pEOT = EOT <$ char '\EOT' <|> EOT <$ char '\ETB'



deserializePacket :: Parser (Payload' a) -> Parser (Packet' a)
deserializePacket pMsg 
  = Packet 
  <$> pChannel 
  <*> emphasized pSeq
  <*> pTab
  <*> pMsg
  <*> pEOT

-------------------------------
-- Main combinators
-------------------------------

emphasized :: Parser a -> Parser a
emphasized = lexeme . between (char '[') (char ']')

