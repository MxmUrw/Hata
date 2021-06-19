
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module MetaBuilder.Project.Type.AgdaPublish.Common where

import Data.Text
import Control.Monad

import System.Exit

type MBRes a = Either String a

assumeRight :: MBRes a -> IO a
assumeRight (Right a) = return a
assumeRight (Left err) = do
  Prelude.putStrLn err
  exitFailure


class TShow a where
  tshow :: a -> Text

instance TShow Text where
  tshow t = t

instance TShow a => TShow [a] where
  tshow as = intercalate "\n" (tshow <$> as)

char_BraceOpen  = '\xe000'
char_BraceClose = '\xe001'
char_Underscore = '\xe002'
char_Backslash = '\xe003'
char_Circumflex = '\xe004'
char_Whitespace = '\xe005'


descape :: String -> String
descape = fmap f
  where f :: Char -> Char
        f '{'  = char_BraceOpen
        f '}'  = char_BraceClose
        f '_'  = char_Underscore
        f '\\' = char_Backslash
        f '^'  = char_Circumflex
        f ' '  = char_Whitespace
        f a    = a

-- restoreChars :: Char -> String

restoreChars :: Char -> String
restoreChars a | a == char_BraceOpen    = "{"
restoreChars a | a == char_BraceClose   = "}"
restoreChars a | a == char_Underscore   = "_"
restoreChars a | a == char_Backslash    = "\\"
restoreChars a | a == char_Circumflex   = "^"
restoreChars a | a == char_Whitespace   = " "
restoreChars '≣' = ['≡']
restoreChars '≡' = ['=']
restoreChars a = [a]

modifyChars :: Char -> String
modifyChars a | a `inRanges` operators = "{" <> [a] <> "}"
    where inRanges :: Ord a => a -> [(a,a)] -> Bool
          inRanges a xs = or ((\(low, high) -> and [low <= a, a <= high]) <$> xs)
          operators :: [(Char,Char)]
          operators = [('∴', '⋿'), ('■','◿'), ('/', '/'), ('-', '-'), ('+', '+')
                      ,('←', '⇿'), ('⟰', '⟿')]
modifyChars a = [a]

prettyChars = modifyChars >=> restoreChars
