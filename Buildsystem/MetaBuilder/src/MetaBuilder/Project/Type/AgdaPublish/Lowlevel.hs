
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module MetaBuilder.Project.Type.AgdaPublish.Lowlevel
  (parseBlockLLs
  -- , writeBlockLLs
  , doParseLL
  , doParseCommands
  , BlockLL (..)
  , Prefixed (..)
  , IsHidden (..)
  , FullSpecial (..)
  , Tag (..)
  , Line
  , TShow (..)
  , Special (..)
  , FullComment (..)
  , ParagraphModality (..))
where

import Debug.Trace

import MetaBuilder.Project.Type.AgdaPublish.Persistent

import Data.Attoparsec.Text as A
import Data.Text as T
import Control.Applicative

import MetaBuilder.Project.Type.AgdaPublish.Common
-- data Line =
--   CommentLL Text
--   | HiddenCodeLL Text
--   | CodeLL Text

-- pLine :: Text -> Line
-- pLine t = case pIsCommentLL t of
--   True -> CommentLL t
--   False -> case pIsHidden t of
--     True -> HiddenCodeLL t
--     False -> CodeLL t
--   where
--     pIsCommentLL :: Text -> Bool
--     pIsCommentLL t = T.isPrefixOf "--" t
--     pIsHidden :: Text -> Bool
--     pIsHidden t = T.isPrefixOf "module " t || T.isPrefixOf "open " t

-- removeEmptyLines :: [Text] -> [Text]
-- removeEmptyLines t = filter (\a -> not (isEmpty a)) t
--   where isEmpty :: Text -> Bool
--         isEmpty t = all (== ' ') (unpack T)

-- generateLine :: Line -> Text
-- generateLine

-- data Line = Line Text Text


data Prefixed a = Prefixed Text a
  deriving (Show, Eq)
type Line = Prefixed Text


instance TShow a => TShow (Prefixed a) where
  tshow (Prefixed t a) = t <> tshow a

data Tag =
  Theorem
  | Lemma
  | Definition
  | Notation
  | Example
  | Remark
  | Hide
  | Corollary
  | Wrapper
  | End
  deriving (Show, Eq)
instance TShow Tag where
  tshow Theorem = "theorem"
  tshow Lemma = "lemma"
  tshow Definition = "definition"
  tshow Notation = "notation"
  tshow Example = "example"
  tshow Remark = "remark"
  tshow Hide = "comment"
  tshow Corollary = "corollary"
  tshow Wrapper = "mywrapper"
  tshow End = undefined -- We do not expect this to be printed!

data IsHidden = IsHidden | NotHidden
  deriving (Show, Eq)

data FullSpecial = FullSpecial IsHidden Special
  deriving (Show, Eq)

data Special =
  Chapter Text
  | Section Text
  | Subsection Text
  | Subsubsection Text
  deriving (Show, Eq)

data ParagraphModality =
  PM_NoNewline
  | PM_ResetAnnotation
  deriving (Show,Eq)

data FullComment = FullComment (Maybe ParagraphModality) [Line]
  deriving (Show,Eq)

data FullModuleDef = FullModuleDef Line Text [Text] Text -- <spaces, keyword> <name> <variables> <keyword>
  deriving (Show,Eq)

data BlockLL =
  TagLL Tag
  | SpecialLL FullSpecial
  | SpecialCommandLL SpecialCommand [Line]
  | CommentLL FullComment
  | HiddenCommentLL
  | HiddenCodeLL [Line]
  | CodeLL Line
  | ModuleLL FullModuleDef
  deriving (Show, Eq)

hidestar :: IsHidden -> Text
hidestar IsHidden = "*"
hidestar NotHidden = ""

instance TShow FullSpecial where
  tshow (FullSpecial hid (Chapter t)) = "\\chapter" <> hidestar hid <> "{" <> t <> "}"
  tshow (FullSpecial hid (Section t)) = "\\section" <> hidestar hid <> "{" <> t <> "}"
  tshow (FullSpecial hid (Subsection t)) = "\\subsection" <> hidestar hid <> "{" <> t <> "}"
  tshow (FullSpecial hid (Subsubsection t)) = "\\subsubsection" <> hidestar hid <> "{" <> t <> "}"


parseWhiteLine :: Parser Text
parseWhiteLine = A.takeWhile (== ' ')

parseWhiteBlockLL :: Parser [Text]
parseWhiteBlockLL = parseWhiteLine `sepBy` endOfLine
----------------------------------------
-- Parsing hidden code
parseHiddenCodeLLLine :: Parser Text
parseHiddenCodeLLLine = tshow <$> (Prefixed <$>
  (string "open "
  -- <|> string "module"
  <|> string "{-#"
  <|> string "infix"
  <|> string "private"
  <|> string "variable"
  <|> string "instance "
  -- <|> string "unquoteDecl "
  ) <*> takeTill isEndOfLine)
                                  -- <|> (Prefixed <$> string "module " <*> takeTill isEndOfLine)
                                  -- <|> (Prefixed <$> string "{-# " <*> takeTill isEndOfLine)
                                  -- )

parseHiddenCodeLL :: Parser (Prefixed Text)
parseHiddenCodeLL = Prefixed <$> A.takeWhile (== ' ') <*> (parseHiddenCodeLLLine <|> parseWhiteLine)

parseHiddenCodeLLPure :: Parser (Prefixed Text)
parseHiddenCodeLLPure = Prefixed <$> A.takeWhile (== ' ') <*> (parseHiddenCodeLLLine)

parseHiddenCodeLLBlockLL :: Parser [Prefixed Text]
parseHiddenCodeLLBlockLL = (:) <$> parseHiddenCodeLLPure <*> many (parseHiddenCodeLL <* endOfLine)
-- parseHiddenCodeLLBlockLL = (:) <$> parseHiddenCodeLLPure <*> (parseHiddenCodeLL `sepBy` (endOfLine))

----------------------------------------
-- Parsing comments
-- parseNoTag :: Parser Text
-- parseNoTag = (\c t -> T.pack [c] <> t) <$> notChar '[' <*> takeTill isEndOfLine

notSpecialChar :: Parser Char
notSpecialChar = satisfy (\a -> and [a /= '[', a /= '=', a /= '|', a /= '#', a /= '\n'])

notAgdaSpecialChar :: Parser Char
notAgdaSpecialChar = satisfy (\a -> and [a /= '(', a /= ')', a /= '[', a /= '=', a /= '|', a /= '#' , a /= '{', a /= '}', a /= '\n', a /= ' ', a /= '"'])


parseNoMarker :: Parser Text
parseNoMarker = (\c t -> T.pack [c] <> t) <$> notSpecialChar <*> takeTill isEndOfLine

parseParagraphModality :: Parser ParagraphModality
parseParagraphModality = (const PM_NoNewline <$> char '>')
                         <|> (const PM_ResetAnnotation <$> char ':')

parseCommentLLLine :: Parser (Maybe ParagraphModality, Text)
parseCommentLLLine = string "--" *> many (char ' ') *> char '|' *> (merge <$> option Nothing pModality <*> (many (char ' ') *> takeTill isEndOfLine)) <* endOfLine
  where merge mod txt = (mod , txt)
        pModality = Just <$> parseParagraphModality

parseCommentLL :: Parser (Prefixed Text)
parseCommentLL = Prefixed <$> A.takeWhile (== ' ') <*> (parseHiddenCommentLLLine)

parseCommentLLPure :: Parser (Prefixed (Maybe ParagraphModality, Text))
parseCommentLLPure = Prefixed <$> A.takeWhile (== ' ') <*> (parseCommentLLLine)


parseCommentLLBlockLL :: Parser FullComment
parseCommentLLBlockLL = merge <$> parseCommentLLPure <*> (many (parseCommentLL <* endOfLine))
  where merge (Prefixed pre (modality,line1)) lines = FullComment modality (Prefixed pre line1:lines)

----------------------------------------
-- Module headers

pParensedPart :: Parser String
pParensedPart = pParensed <|> pDoubleBraced <|> pBraced <|> many1 (satisfy p)
  where p :: Char -> Bool
        p a = a `notElem` ['(', ')', '{', '}']

pParensed :: Parser String
pParensed = f <$> (char '(' *> many1 pParensedPart <* char ')')
  where f s = "(" <> Prelude.concat s <> ")"

pBraced :: Parser String
pBraced = f <$> (char '{' *> many1 pParensedPart <* char '}')
  where f s = "{" <> Prelude.concat s <> "}"

pDoubleBraced :: Parser String
pDoubleBraced = f <$> (string "{{" *> many1 pParensedPart <* string "}}")
  where f s = "{{" <> Prelude.concat s <> "}}"

pVariableDecls :: Parser [Text]
pVariableDecls = f <$> many ((pParensed <|> pDoubleBraced <|> pBraced) <* (many1 (char ' ')))
  where f s = (T.pack <$> s)

pModule :: Parser FullModuleDef
pModule = FullModuleDef <$> skipAfter pKeyword
                        <*> skipAfter (T.pack <$> many1 notAgdaSpecialChar)
                        <*> (pVariableDecls)
                        <*> string "where"
                        <* endOfLine
  where pKeyword = Prefixed <$> A.takeWhile (== ' ') <*> string "module"
        skipAfter p = p <* many1 (char ' ')

----------------------------------------
-- Special commands

pFormat :: Parser FontStyle 
pFormat = (const MathRM <$> string "mathrm")
        <|> (const MathBF <$> string "mathbf")

spaceTerm :: Parser a -> Parser a
spaceTerm p = p <* many1 (char ' ')

pCommand_NotationSC2 :: Parser BlockLL
pCommand_NotationSC2 = merge <$> spaceTerm (string "unquoteDecl")
                             <*> spaceTerm (many1 notAgdaSpecialChar)
                             <*> spaceTerm (many1 notAgdaSpecialChar)
                             <*> spaceTerm (string "=")
                             <*> spaceTerm (string "#struct")
                             <*> spaceTerm (char '"' *> many1 notAgdaSpecialChar <* char '"')
                             <*> spaceTerm (string "(quote " *> many1 notAgdaSpecialChar <* char ')')
                             <*> takeTill isEndOfLine
                             <* endOfLine
                            --  <*> spaceTerm (char '"' *> many1 notAgdaSpecialChar <* char '"')
  where merge _ strName ctorName _ _ shortName strIName rest =
          SpecialCommandLL (NotationSC MathRM shortName strName)
                            [Prefixed "" (T.pack ("unquoteDecl " <> strName <> " " <> ctorName
                                          <> " = #struct "
                                          <> "\"" <> shortName <> "\" "
                                          <> "(quote " <> strIName <> ") "
                                          <> T.unpack rest))]

pCommand_NotationSC :: Parser BlockLL
pCommand_NotationSC = embed $ string "--" *> many (char ' ') *> string "#Notation/SemanticCategory#" *> many1 (char ' ')
                      *> (NotationSC <$> (char '\\' *> pFormat <* char '{')
                                     <*> (many1 notAgdaSpecialChar) <* string "} = "
                                     <*> (T.unpack <$> takeTill isEndOfLine))
                                     <* endOfLine
    where embed x = (\a -> SpecialCommandLL a []) <$> x

pCommand_NotationSA :: Parser BlockLL
pCommand_NotationSA = embed $ string "--" *> many (char ' ') *> string "#Notation/Annotatable#" *> many1 (char ' ')
                               *> (NotationSA <$> (many1 notAgdaSpecialChar)) <* endOfLine
    where embed x = (\a -> SpecialCommandLL a []) <$> x

pCommand_NotationRewrite :: Parser BlockLL
pCommand_NotationRewrite = embed $ string "--" *> many (char ' ') *> string "#Notation/Rewrite#" *> many1 (char ' ')
                               *> (f <$> spaceTerm (many1 notAgdaSpecialChar)
                                     <*> spaceTerm (string "=") 
                                     <*> many1 (satisfy (`notElem` [' ', '\n'])))
                               <* endOfLine
    where embed x = (\a -> SpecialCommandLL a []) <$> x
          f s1 _ s2 = NotationRewrite s1 s2

 
pCommand :: Parser BlockLL
pCommand = (pCommand_NotationSC <?> "special command (SC)")
          <|> (pCommand_NotationSA <?> "special command (SA)")
          <|> (pCommand_NotationSC2 <?> "special command by #struct macro")
          <|> (pCommand_NotationRewrite <?> "special command (rewrite)")


----------------------------------------
-- Hidden comments

------ single line
parseHiddenCommentLLLine :: Parser Text
parseHiddenCommentLLLine = string "--" *> many (char ' ') *> (parseNoMarker) -- takeTill isEndOfLine

parseHiddenCommentLL :: Parser (Prefixed Text)
parseHiddenCommentLL = Prefixed <$> A.takeWhile (== ' ') <*> (parseHiddenCommentLLLine <|> parseWhiteLine)

parseHiddenCommentLLPure :: Parser (Prefixed Text)
parseHiddenCommentLLPure = Prefixed <$> A.takeWhile (== ' ') <*> (parseHiddenCommentLLLine)

parseHiddenCommentLLBlockLL :: Parser [Prefixed Text]
parseHiddenCommentLLBlockLL =  ((:) <$> parseHiddenCommentLLPure <*> (many (parseHiddenCommentLL <* endOfLine)) <?> "Hidden Comment")
                            <|> (string "--" *> many (char ' ') *> endOfLine *> pure ([Prefixed "" ""]))

------ multiline version
parseMultilineComment :: Parser Text
parseMultilineComment = T.pack <$> (A.takeWhile (== ' ') *> string "{-" *> manyTill' anyChar (string "-}")) <?> "Multiline comment"

----------------------------------------
-- Parsing tags

parseEndTag :: Parser Tag
parseEndTag = (\_ -> End) <$> (A.takeWhile (== ' ') *> string "--" *> A.skipSpace *> string "//" <* takeTill isEndOfLine <* endOfLine)

parseTag :: Parser Tag
parseTag = ((\_ -> Definition) <$> string "Definition")
           <|> ((\_ -> Theorem) <$> string "Theorem")
           <|> ((\_ -> Notation) <$> string "Notation")
           <|> ((\_ -> Example) <$> string "Example")
           <|> ((\_ -> Remark) <$> string "Remark")
           <|> ((\_ -> Lemma) <$> string "Lemma")
           <|> ((\_ -> Corollary) <$> string "Corollary")
           <|> ((\_ -> Wrapper) <$> string "Wrapper")
           <|> ((\_ -> Hide) <$> string "Hide")


parseTagLLLine :: Parser Tag
parseTagLLLine = A.takeWhile (== ' ') *> string "--" *> A.skipSpace *> char '[' *> parseTag <* char ']' <* takeTill isEndOfLine <* endOfLine

{-
parseEqLine :: Parser ()
parseEqLine = (string "--==========================================" *> many (char '=') *> endOfLine)

parseMinusLine :: Parser ()
parseMinusLine = (string "------------------------------------------" *> many (char '-') *> endOfLine)

parseShortMinusLine :: Parser ()
parseShortMinusLine = (string "----------------" *> many (char '-') *> endOfLine)

parseSpecial :: Parser Special
parseSpecial = (Chapter <$> (parseEqLine *> string "--" *> skipWhile (== ' ') *> takeTill isEndOfLine <* endOfLine <* parseEqLine))
               <|> (Section <$> (parseMinusLine *> string "--" *> skipWhile (== ' ') *> takeTill isEndOfLine <* endOfLine))
               <|> (Subsection <$> (parseShortMinusLine *> string "--" *> skipWhile (== ' ') *> takeTill isEndOfLine <* endOfLine))
-}



parseSpecial :: Parser FullSpecial
parseSpecial = (FullSpecial NotHidden <$> pNH) <|> (FullSpecial IsHidden <$> pH)
              --  <|> (Section <$> (string "--" *> many (char ' ') *> string "==" *> many1 (char ' ') *> takeTill isEndOfLine))
              --  <|> (Subsection <$> (string "--" *> many (char ' ') *> string "===" *> many1 (char ' ') *> takeTill isEndOfLine))
              --  <|> (Subsubsection <$> (string "--" *> many (char ' ') *> string "====" *> many1 (char ' ') *> takeTill isEndOfLine)))
    where p intro = string "--" *> many (char ' ') *> string intro *> many1 (char ' ') *> takeTill isEndOfLine
          pNH = (Chapter <$> p "=")
                <|> (Section <$> p "==")
                <|> (Subsection <$> p "===")
                <|> (Subsubsection <$> p "====")
          pH  = (Chapter <$> p "=*")
                <|> (Section <$> p "==*")
                <|> (Subsection <$> p "===*")
                <|> (Subsubsection <$> p "====*")


---------------------------------------
-- Parse simple code
isValidCodeBegin :: Char -> Bool
isValidCodeBegin a = and [a /= '-', a /= '\n']

parseCodeBegin :: Parser (Prefixed (Char,Char))
parseCodeBegin = Prefixed <$> A.takeWhile (== ' ') <*> ((,) <$> satisfy isValidCodeBegin <*> anyChar)

parseCodeBeginAlt :: Parser (Prefixed (Char,Char))
parseCodeBeginAlt = Prefixed <$> A.takeWhile (== ' ') <*> ((,) <$> anyChar <*> satisfy isValidCodeBegin)

mergeCode :: (Prefixed (Char, Char), Text) -> Text
mergeCode (Prefixed pre (a, b), t) = pre <> T.pack (a : b : []) <> t

parseCode :: Parser Text
parseCode = mergeCode <$> ((,) <$> (parseCodeBegin <|> parseCodeBeginAlt) <*> takeTill isEndOfLine)

-- parse a line of code with only a single non-white symbol
parseCode1 :: Parser Text
parseCode1 = (\pre a -> pre <> T.pack [a]) <$> A.takeWhile (== ' ') <*> satisfy isValidCodeBegin

parseCodeLLLine :: Parser Text
parseCodeLLLine = (parseCode <|> parseCode1) <* endOfLine

parseCodeLLBlockLL :: Parser (Prefixed Text)
parseCodeLLBlockLL = Prefixed "" <$> parseCodeLLLine <?> "CodeBlock"

---------------------------------------
-- Parsing blocks
parseBlockLL :: Parser BlockLL
parseBlockLL = (TagLL <$> parseTagLLLine)
            <|> (TagLL <$> parseEndTag)
            <|> (SpecialLL <$> parseSpecial)
            <|> (pCommand)
            <|> (ModuleLL <$> pModule)
            <|> (HiddenCodeLL <$> parseHiddenCodeLLBlockLL) -- This has to come before 'parseMultiLineComment' because {- and {-# overlap
            <|> (CommentLL <$> parseCommentLLBlockLL)
            <|> ((\_ -> HiddenCommentLL) <$> parseHiddenCommentLLBlockLL)
            <|> ((\_ -> HiddenCommentLL) <$> parseMultilineComment)
            <|> (CodeLL <$> parseCodeLLBlockLL)

-- parseBlockLL = (SpecialCommandLL <$> pCommand)
--             <|> (CommentLL <$> parseCommentLLBlockLL)

parseBlockLLs :: Parser ([BlockLL], Text)
parseBlockLLs = (,) <$> (parseWhiteBlockLL *> (many (parseBlockLL <* many endOfLine))) <*> takeText -- <* endOfInput


-------------------------------------
-- Testing output


writeBlockLL :: BlockLL -> Text
writeBlockLL (CommentLL (FullComment mod t)) = "CommentLL(" <> T.pack (show mod) <> "): " <> T.intercalate "\n" (tshow <$> t) <> "End comment."
writeBlockLL (HiddenCodeLL t) = "Hidden code: " <> T.intercalate "\n" (tshow <$> t) <> "End hidden code."
writeBlockLL (CodeLL t) = "CodeLL: " <> tshow t <> "\n"
writeBlockLL (TagLL t) = "Tag: " <> T.pack (show t) <> "\n"
writeBlockLL (SpecialLL (FullSpecial hid t)) = "SpecialLL: " <> T.pack (show t <> "(" <> show hid <> ")") <> "\n"
writeBlockLL (SpecialCommandLL t lines) = "SpecialCommand: " <> T.pack (show t) <> "\n" <> "  - lines: " <> tshow lines
writeBlockLL (HiddenCommentLL) = "HiddenComment\n"
writeBlockLL (ModuleLL full) = "ModuleDef: " <> T.pack (show full)

writeBlockLLs :: [BlockLL] -> Text
writeBlockLLs bs = T.intercalate "" (writeBlockLL <$> bs)

-- isCommand :: BlockLL -> Bool
-- isCommand (SpecialCommandLL _) = True
-- isCommand _ = False

expandCommand :: SpecialCommand -> [SpecialCommand]
expandCommand (NotationSA name) = [NotationSA name]
expandCommand (NotationSC fmt replacement toBeReplaced) =
   [NotationSC_Short MathBF replacement toBeReplaced
   , NotationSC_Short MathBF  ("is" <> replacement) ("I" <> toBeReplaced)
   , NotationSC MathRM ("is" <> toBeReplaced) ("I" <> toBeReplaced)
   , NotationSC MathRM (toBeReplaced) (toBeReplaced) ] 
expandCommand (NotationSC_Short fmt r t) = [NotationSC_Short fmt r t]
expandCommand (NotationRewrite s1 s2) = [NotationRewrite s1 s2] -- NOTE: We actually should check that |s1| <= |s2|

getCode :: BlockLL -> [BlockLL]
getCode (SpecialCommandLL cmd lines) = [HiddenCodeLL lines]
getCode (ModuleLL (FullModuleDef (Prefixed pre key_mod) name vars key_where)) =
  [ HiddenCodeLL [Prefixed pre (key_mod <> " " <> name)] ]
  <> ((\a -> CodeLL (Prefixed (pre <> "  ") a)) <$> vars)
  <> [ HiddenCodeLL [Prefixed (pre <> "    ") key_where] ]
  --   CodeLL (Prefixed (pre <> "  ") vars),
  -- ]
getCode b = [b]

getCommands :: BlockLL -> [SpecialCommand]
getCommands (SpecialCommandLL a lines) = [a]
getCommands r = []

parseFull :: Text -> Either String [BlockLL]
parseFull t = parseOnly parseBlockLLs t >>= f
  where f :: ([BlockLL], Text) -> Either String [BlockLL]
        f (good, "") = Right good -- Right (trace ("\nParsed lowlevel:\n" <> T.unpack (writeBlockLLs good)) good)
        f (good, rest) = Left $ "Error when parsing: The following rest could not be parsed:\n" ++ Prelude.unlines (Prelude.take 3 (Prelude.lines (T.unpack rest)))

doParseLL :: Text -> Either String [BlockLL]
doParseLL t = (getCode =<<) <$> parseFull t

doParseCommands :: Text -> Either String [SpecialCommand]
doParseCommands t = (>>= expandCommand) <$> (>>= getCommands) <$> parseFull t


