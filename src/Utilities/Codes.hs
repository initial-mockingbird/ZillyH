{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ImportQualifiedPost      #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE CPP                      #-}

{-# LANGUAGE TemplateHaskell          #-}


module Utilities.Codes where


-- | Server response content format
data ServerResponseCodes
  = OK
  | ACK
  | ERROR

-- | Server notification content format
data ServerNotificationCodes
  = SYM
  | SYP
  | SYU
  | ASY

data ServerResponse m a where
  OKR    :: forall expression result m. expression -> result -> ServerResponse m OK
  ACKR   :: forall action m. action -> ServerResponse m ACK
  ERRORR :: String -> ServerResponse m ERROR
