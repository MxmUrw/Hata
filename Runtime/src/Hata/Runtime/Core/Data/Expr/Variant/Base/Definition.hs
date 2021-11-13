
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Core.Data.Expr.Variant.Base.Definition where

import Data.Text as T
import Data.HashMap.Strict as H
import Data.Void

-- parser
import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Applicative hiding (many, some)

import Hata.Runtime.Core.Data.SourceCode.Variant.Tokenized.Definition

type Parser = Parsec Void Text

data BaseExpr a x = Hole x | Var Text | Token a | List [BaseExpr a x]

parseBaseExpr :: HasElementNames a -> Text -> Either Text (BaseExpr a Text)
parseBaseExpr hen input = case runParser (pTokenBaseExpr hen) "input" input of
  Left err -> Left $ T.pack $ errorBundlePretty err
  Right x -> Right x

pTokenBaseExpr :: forall a. HasElementNames a -> Parser (BaseExpr a Text)
pTokenBaseExpr def = List <$> (space *> pBaseExprs <* eof)
  where
    pBaseExpr :: Parser (BaseExpr a Text)
    pBaseExpr = try pParensedBaseExpr <|> try pToken <|> pVar

    pBaseExprs :: Parser [BaseExpr a Text]
    pBaseExprs = many (pBaseExpr <* space)

    pParensedBaseExpr :: Parser (BaseExpr a Text)
    pParensedBaseExpr = between (char '(') (char ')') (List <$> pBaseExprs)

    pToken :: Parser (BaseExpr a Text)
    pToken = Token <$> pCon

    pCon :: Parser a
    pCon = choice (p <$> tokenValues def)
      where
        p :: a -> Parser a
        p a = try (string (nameOfToken def a) *> pure a)

    pVar :: Parser (BaseExpr a Text)
    pVar = Var <$> pIdentifier

    pIdentifier :: Parser Text
    pIdentifier = label "identifier" $
      T.pack <$> some (noneOf [' ', '\n', '\r', '\t', '(', ')'])


