{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE OverloadedStrings   #-}

{-|
Module      : Lilly.Parser.IR.IRPatterns
Description : Common Pattern Synonyms for the IR.
Copyright   : (c) Daniel Pinto, 2024
                  Enzo Alda, 2024
License     : GPL-3
Maintainer  : daniel.andres.pinto@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Lilly.Parser.IR.IRPatterns where

import Lilly.Parser.IR.TH ( genOpPatterns, stdTable )   

$(genOpPatterns stdTable)