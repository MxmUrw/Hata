
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Experimental.Theory.Std.Presentation.Token.Definition where

import Data.Text as T

data TokenDefinition a = TokenDefinition [a] (a -> Text)

data Tree a b = Node a [Tree a b] | Var b

parseTokens :: TokenDefinition a -> Text -> Tree a Text
parseTokens def t = Var "something"




