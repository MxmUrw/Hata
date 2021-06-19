
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module MetaBuilder.Project.Type.AgdaPublish.MidlevelCode
  -- (doParseML
  -- , TShow (..)
  -- , BlockML (..)
  -- )
  where

import Debug.Trace

import Data.Text as T
import Data.Char
import Data.Text.IO as TIO
-- import Control.Applicative
import Agda.Interaction.Highlighting.LaTeX.ExternalCall
import Agda.Interaction.Highlighting.LaTeX.Prettify
import Agda.Interaction.Highlighting.Precise

import Text.Parsec hiding (Line)

import MetaBuilder.Project.Type.AgdaPublish.Highlevel
import MetaBuilder.Project.Type.AgdaPublish.Common
import MetaBuilder.Project.Type.AgdaPublish.Persistent


-- code snippets in comments
data AgdaTerm =
  LocalVariableAT Text
  | FunctionAT Text
  | ParensedAT [AgdaTerm]
  deriving (Show)

pWhitespace :: Parsec Text () Text
pWhitespace = T.pack <$> many1 (char ' ')

notQuoteEnd :: Char -> Bool
notQuoteEnd = (/=) '|'

validNameChar :: Char -> Bool
validNameChar a = and [a `notElem` ['(',')',' '], notQuoteEnd a]

pSmallOperator :: Parsec Text () AgdaTerm
pSmallOperator = FunctionAT . T.pack . (:[]) <$> satisfy validNameChar

pVar :: Parsec Text () AgdaTerm
pVar = LocalVariableAT . T.pack . (:[]) <$> satisfy (\a -> and [isAlpha a, notQuoteEnd a])

pFunction :: Parsec Text () AgdaTerm
pFunction = merge <$> satisfy validNameChar <*> many1 (satisfy validNameChar)
  where merge c cs = FunctionAT $ T.pack $ (c : cs)

pParensed :: Parsec Text () AgdaTerm
pParensed = ParensedAT <$> between (char '(') (char ')') (pToplevel)

pTerm :: Parsec Text () AgdaTerm
-- pTerm = (withnext pVar) <|> (withnext pFunction) <|> (withnext pParensed)
pTerm = (try pFunction) <|> try pVar <|> try pSmallOperator <|> (try pParensed)

pToplevel :: Parsec Text () [AgdaTerm]
pToplevel = sepBy1 pTerm pWhitespace

type ToplevelAT = [AgdaTerm]

data AgdaToken = AgdaToken (Maybe Aspect) Text
  deriving (Show)

instance TokenLike AgdaToken where
  getTokenText (AgdaToken _ s) = s
  setTokenText (AgdaToken a s) t = (AgdaToken a t)
  makePlainToken a t = AgdaToken a t

intoTokenMultiple :: [AgdaTerm] -> [AgdaToken]
intoTokenMultiple [] = []
intoTokenMultiple (a : []) = intoToken a
intoTokenMultiple (a : as) = intoToken a <> [AgdaToken Nothing " "] <> intoTokenMultiple as

intoToken :: AgdaTerm -> [AgdaToken]
intoToken (ParensedAT ts) = [AgdaToken Nothing "("] <> intoTokenMultiple ts <> [AgdaToken Nothing ")"]
intoToken (FunctionAT f) = [AgdaToken (Just (Name (Just Function) False)) f]
intoToken (LocalVariableAT v) = [AgdaToken (Just (Name (Just Bound) True)) v]

parseAgdaTokens :: Parsec Text () AgdaTokens
parseAgdaTokens = f <$> pToplevel
  where f tms = AgdaTokens $ intoTokenMultiple tms

printToken :: AgdaToken -> Text
printToken = impl
  where impl :: AgdaToken -> Text
        impl (AgdaToken Nothing t) = pretty t
        impl (AgdaToken (Just (Name Nothing _)) t) = (pretty t)
        impl (AgdaToken (Just (Name (Just x) _)) t) = wrapWith (show x) (pretty t)
        impl (AgdaToken (Just (MetabuilderAspect s)) t) = wrapWith (T.unpack s) (pretty t)
        impl (AgdaToken (Just a) t) = wrapWith (show a) (pretty t)

        replaceWhite :: Char -> String
        replaceWhite ' ' = "\\AgdaSpace{}"
        replaceWhite c = [c]

        pretty :: Text -> Text
        pretty t = T.pack $ replaceWhite =<< prettyChars =<< T.unpack t

        wrapWith :: String -> Text -> Text
        wrapWith wrapper t = "\\Agda" <> T.pack wrapper <> "{" <> t <> "}"

data AgdaTokens = AgdaTokens [AgdaToken]
  deriving (Show)

instance TShow AgdaTokens where
  tshow (AgdaTokens at) = 
    let
      strs = printToken <$> at
      str = T.concat strs
    in str

-- removeTrailingWSTok :: AgdaToken -> AgdaToken
-- removeTrailingWSTok a = (f a)
--   where f t | isWhitespace t = t
--         f t | otherwise      = setTokenText t (T.strip (getTokenText t))

-- removeTrailingWS :: [AgdaToken] -> [AgdaToken]
-- removeTrailingWS xs = fmap removeTrailingWSTok xs
  -- Prelude.reverse (f (Prelude.reverse xs))
  -- where f [] = []
  --       f (x : xs) = removeTrailingWSTok x : xs

  
processTerm :: [SpecialCommand] -> AgdaTokens -> AgdaTokens
processTerm cmd (AgdaTokens at) = AgdaTokens $ removeTrailingWS $ parseAndGenerate cmd at

