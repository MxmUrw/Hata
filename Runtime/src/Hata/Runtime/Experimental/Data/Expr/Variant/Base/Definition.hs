
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Experimental.Theory.Std.Presentation.Token.Definition where

import Data.Text as T
import Data.HashMap.Strict as H
import Data.Void

-- parser
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Applicative hiding (many, some)

type Parser = Parsec Void Text

data HasElementNames a = HasElementNames
  { tokens :: [a]
  , nameOfToken :: (a -> Text)
  }

data BaseExpr a v x = Hole x | Var v | Token a | List (BaseExpr a v x)

parseTokens :: HasElementNames a -> Text -> Either Text (BaseExpr a Text ())
parseTokens = undefined



