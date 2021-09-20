
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Experimental.Theory.Std.Presentation.Token.Definition where

import Data.Text as T
import Data.HashMap.Strict as H

-- parser
import Text.Parsec
import Text.Parsec.Text

data TokenDefinition a = TokenDefinition
  { constructors :: [a]
  , nameOfCon :: (a -> Text)
  }

data Tree a b = Node a [Tree a b] | Var b

doParse :: Parser a -> Text -> Either Text a
doParse p t = case runParser p () "<source>" (t) of
                      Left err -> Left $ T.pack $ show err
                      Right x -> Right x

parseTokens :: TokenDefinition a -> Text -> Either Text (Tree a Text)
parseTokens def = doParse (pTokenTree def)

parseTwolines :: TokenDefinition a -> Text -> Either Text (Tree a Text, Tree a Text)
parseTwolines def t = doParse ((,) <$> (pTokenTree def <* many1 space) <*> (pTokenTree def <* many1 space <* eof)) t

pTokenTree :: forall a. TokenDefinition a -> Parser (Tree a Text)
pTokenTree def = pTree
  where
    pTree :: Parser (Tree a Text)
    pTree = try pNode <|> pVar

    pParensedTree :: Parser (Tree a Text)
    pParensedTree = between (char '(') (char ')') pTree

    pNode :: Parser (Tree a Text)
    pNode = Node <$> pCon <*> many (pEmpty *> pParensedTree)

    pCon :: Parser a
    pCon = choice (p <$> constructors def)
      where
        p :: a -> Parser a
        p a = try (string (T.unpack $ nameOfCon def a) *> pure a)

    pVar :: Parser (Tree a Text)
    pVar = Var <$> T.pack <$> many1 pSymbol

    pSymbol :: Parser Char
    pSymbol = noneOf [' ', '\n', '\t', '(' , ')']

    pEmpty :: Parser String
    pEmpty = many1 (char ' ')


-------
-- Containers / Hashmap

type TextHashMap = HashMap Text

data IsContainer k v d = IsContainer d (k -> d -> Either () v) (k -> v -> d -> d)

isContainer_TextHashMap :: IsContainer Text v (HashMap Text v)
isContainer_TextHashMap = IsContainer
  H.empty
  (\a b -> co (H.lookup a b))
  (H.insert)
  where
    co (Just a) = Right a
    co (Nothing) = Left ()




