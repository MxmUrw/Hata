
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Application.Persistent.ContentFile where

import Data.Text as T
import Data.Void

-- parser
import Text.Megaparsec
import Text.Megaparsec.Char
-- import Text.Megaparsec.Char.Lexer (lexeme)
import Control.Applicative hiding (many, some)

type Parser = Parsec Void Text

data BaseContentFile = BaseContentFile Text Text


parseContentFile :: Text -> Either Text BaseContentFile
parseContentFile input = case runParser pContentFile "input" input of
  Left err -> Left $ T.pack $ errorBundlePretty err
  Right x -> Right x

pContentFile :: Parser BaseContentFile
pContentFile = space >> (BaseContentFile <$> pLanguage <*> takeRest)

pLanguage :: Parser Text
pLanguage = string "-- LANGUAGE:" >> hspace1 >> pIdentifier <* hspace <* newline

pIdentifier :: Parser Text
pIdentifier = label "identifier" $
  T.pack <$> some (noneOf [' ', '\n', '\r', '\t'])


