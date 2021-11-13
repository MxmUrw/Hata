
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Core.Data.SourceCode.Variant.Tokenized.Definition where

import Data.Text as T
import Data.HashMap.Strict as H
import Data.Void

-- parser
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Applicative hiding (many, some)


data HasElementNames a = HasElementNames
  { tokenValues :: [a]
  , nameOfToken :: (a -> Text)
  }



