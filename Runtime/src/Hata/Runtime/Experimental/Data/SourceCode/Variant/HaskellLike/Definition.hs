
{-# LANGUAGE OverloadedStrings #-}

module Hata.Runtime.Experimental.Data.SourceCode.Variant.HaskellLike.Definition where

import Data.Text as T
import Data.HashMap.Strict as H
import Data.Void

-- parser
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Debug
import Control.Applicative hiding (many, some)

type Parser = Parsec Void Text


data HaskellLikeSourceCode x =
  Var x
  | NewLine Integer
  | Horizontal [Either Integer (HaskellLikeSourceCode x)]
  | Vertical Integer [HaskellLikeSourceCode x]


-- SNewLine "Number of spaces after newline"
-- HSpace "Number of (horizontal) spaces"
-- EmptyLine "Number of empty lines" (`number of \n` - 1)
data Space = SNewLine Int | HSpace Int | EmptyLine Int
  deriving (Show)

data SourceExpr =
  SVar Text
  | SList [Either Space (SourceExpr)]
  | SWhere Int

type SpaceSourceExpr = Either Space (SourceExpr)


parseHaskellLikeSourceCode :: Text -> Either Text (HaskellLikeSourceCode Text)
parseHaskellLikeSourceCode input = fmap (processSingle 0) (parseSourceExpr input)

-- pTokenHaskellLikeSourceCode def = List <$> (space *> pHaskellLikeSourceCodes <* eof)

parseSourceExpr :: Text -> Either Text (SourceExpr)
parseSourceExpr input = case runParser (pSourceExpr) "input" input of
  Left err -> Left $ T.pack $ errorBundlePretty err
  Right x -> Right x

pSourceExpr :: Parser (SourceExpr)
pSourceExpr = pTop <* eof
  where
    pTop :: Parser (SourceExpr)
    pTop = SList <$> pItems

    pItems :: Parser [Either Space (SourceExpr)]
    pItems = many (try (Right <$> pNonSpace) <|> try (Left <$> pSpace))
      -- where
        -- both a b = f <$> (many ((,) <$> a <*> b))
        -- f [] = []
        -- f ((a,b):xs) = a:b:f xs

    pParensedItems :: Parser (SourceExpr)
    pParensedItems = between (char '(') (char ')') (SList <$> pItems)


    ------
    -- parsing space
    pCountSpace :: Parser Int
    pCountSpace = Prelude.length <$> some (char ' ')

    pCountSpace' :: Parser Int
    pCountSpace' = Prelude.length <$> many (char ' ')

    pCountEmptyLine :: Parser Int
    pCountEmptyLine = (Prelude.length <$> some (try (newline >> hspace >> lookAhead (newline >> (return ' ')))))

    pSpace :: Parser Space
    pSpace = try pEmpty <|> try pNew <|> try pHSpace
      where
        pHSpace :: Parser Space
        pHSpace = HSpace <$> pCountSpace

        pNew :: Parser Space
        pNew = newline *> (SNewLine <$> pCountSpace')

        pEmpty :: Parser Space
        pEmpty = EmptyLine <$> pCountEmptyLine

    -------
    -- parsing non space

    pNonSpace :: Parser (SourceExpr)
    pNonSpace = try pParensedItems <|> try pWhere <|> try pVar

    pWhere :: Parser (SourceExpr)
    pWhere = string "where" >> newline >> (SWhere <$> pCountSpace')

    -- pToken :: Parser (SourceExpr)
    -- pToken = SToken <$> pCon

    -- pCon :: Parser a
    -- pCon = choice (p <$> tokenValues def)
    --   where
    --     p :: a -> Parser a
    --     p a = try (string (nameOfToken def a) *> pure a)

    pVar :: Parser (SourceExpr)
    pVar = SVar <$> pIdentifier

    pIdentifier :: Parser Text
    pIdentifier = label "identifier" $
      T.pack <$> some (noneOf [' ', '\n', '\r', '\t', '(', ')'])



processSingle :: Int -> SourceExpr -> HaskellLikeSourceCode Text
processSingle n (SVar t) = Var t
-- processSingle n (SToken t) = Token t
processSingle n (SList t) = Horizontal (processHorizontal n t)
processSingle n (SWhere t) = Var "where"

processHorizontal :: Int -> [SpaceSourceExpr] -> [Either Integer (HaskellLikeSourceCode Text)]
processHorizontal b [] = []
processHorizontal b (Right (SWhere n) : xs) | b < n  =
  let isLessIndented (Left (SNewLine i)) | (i <= b) = Just i
      isLessIndented _ = Nothing

      -- we call this equal, but we catch all {i | b < i <= n}
      isEqualIndented (Left (SNewLine i)) | (i <= n) = Just i
      isEqualIndented _ = Nothing

      (this,rest) = case splitFirst isLessIndented xs of
                      Just (relevant,sep,rest) -> (relevant, rest)
                      Nothing -> (xs,[])

      (fstL,othL) = splitAll isEqualIndented this
      allThisLines = fstL : (snd <$> othL)
      processedLines = (processSingle n . SList) <$> allThisLines
      resultProcessed = Vertical (fromIntegral n) processedLines

      restProcessed = processHorizontal b rest

  in (Right resultProcessed:restProcessed)
processHorizontal b (Right (SWhere n) : xs) | b >= n = processHorizontal b xs
processHorizontal b (Right x : xs) = Right (processSingle b x) : processHorizontal b xs
processHorizontal b (Left (HSpace n) : xs) = processHorizontal b xs
processHorizontal b (Left (SNewLine n) : xs) = Left (fromIntegral n) : processHorizontal b xs
processHorizontal b (Left (EmptyLine n) : xs) = Right (NewLine (fromIntegral n)) : processHorizontal b xs
-- Right (Var $ "[emptyline " <> T.pack (show n) <> "]") : 

splitFirst :: (a -> (Maybe b)) -> [a] -> Maybe ([a],b,[a])
splitFirst f xs = fmap i $ dosplit f xs []
  where
    dosplit :: (a -> (Maybe b)) -> [a] -> [a] -> Maybe ([a],b,[a])
    dosplit f [] acc = Nothing
    dosplit f (x:xs) acc = case (f x) of
      Nothing -> dosplit f xs (x:acc)
      Just b -> Just (acc,b,xs)

    i (acc,x,xs) = (Prelude.reverse acc,x,xs)

splitAll :: (a -> (Maybe b)) -> [a] -> ([a],[(b, [a])])
splitAll f xs = dosplit f xs
  where
    dosplit :: (a -> Maybe b) -> [a] -> ([a],[(b, [a])])
    dosplit f xs = case splitFirst f xs of
                     Nothing -> (xs,[])
                     Just (xs,b,as) -> let (as2,bas) = dosplit f as
                                       in (xs,((b,as2) : bas))

-- splitNewlines :: Int -> Int -> [SpaceSourceExpr] -> ([SpaceSourceExpr],[SpaceSourceExpr])
-- splitNewlines prev cur [] acc = ([],[])
-- splitNewlines prev cur (Left (SNewLine n):xs) acc | n <= prev = (acc,xs)
-- splitNewlines prev cur (Left (SNewLine n):xs) acc | n <= prev = (acc,xs)


  -- SVar Text
  -- SToken a
  -- SList [Either Space (SourceExpr)]
  -- SWhere Int
