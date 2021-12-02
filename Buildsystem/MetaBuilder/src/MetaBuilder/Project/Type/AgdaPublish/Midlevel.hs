{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module MetaBuilder.Project.Type.AgdaPublish.Midlevel
  (doParseML
  , TShow (..)
  , BlockML (..)
  )
  where

import Debug.Trace

import Data.Text as T
import Data.Text.IO as TIO
-- import Control.Applicative

import Text.Parsec hiding (Line)

import MetaBuilder.Project.Type.AgdaPublish.Lowlevel

import MetaBuilder.Project.Type.AgdaPublish.MidlevelCode
import MetaBuilder.Project.Type.AgdaPublish.Persistent
-- instance TShow a => TShow [a] where
--   tshow as = T.intercalate "\n" (tshow <$> as)

data BlockML =
  CommentML Paragraph
  | HiddenCodeML [Line]
  | CodeML [Line]
  | SpecialML FullSpecial
  deriving (Show)

--- | TagML Tag
data BlockFlat =
  CommentFlat ParagraphFlat
  | HiddenCodeFlat [Line]
  | CodeFlat Wildcard [Line]
  | SpecialFlat FullSpecial
  | NewlineFlat
  | SpaceFlat
  deriving (Show)

instance MapCommentPart BlockFlat where
  mapcp f (CommentFlat pf) = CommentFlat (mapcp f pf)
  mapcp f a = a


prettifyCode :: Text -> Text
prettifyCode = (T.replace "->" "→")

filterEmptyLines :: [Prefixed Text] -> [Prefixed Text]
filterEmptyLines = Prelude.filter isNotEmpty
  where isNotEmpty :: Prefixed Text -> Bool
        isNotEmpty (Prefixed _ t) = t /= ""


instance TShow Wildcard where
  tshow InlineHidden = "[hide]"
  tshow Inline = "[inline]"
  tshow (Ownline _) = ""

setTrailingCmd :: Text -> Text
setTrailingCmd t = "\\renewcommand{\\AgdaTrailingText}{" <> val <> "}%\n"
  where val = "\\>[25]" <> "\\textrm{" <> t <> "}" <> "\\<"

wildcardPrePost :: Wildcard -> (Text,Text)
wildcardPrePost Inline = ("\\begin{code}[inline]%\n","\\end{code}%\n{}")
wildcardPrePost InlineHidden = ("\\begin{code}[hide]%\n","\\end{code}%\n{}")
wildcardPrePost (Ownline "") = ("\\begin{code}%\n", "\\end{code}%\n")
wildcardPrePost (Ownline trailing) = (setTrailingCmd trailing <> "\\begin{code}%\n", "\\end{code}%\n")

instance TShow BlockFlat where
  tshow (CommentFlat lines) = (tshow lines)
  tshow (HiddenCodeFlat lines) = "\\begin{code}[hide]\n" <> T.intercalate "\n" (tshow <$> lines) <> "\n\\end{code}%\n{}"
  tshow (CodeFlat wild lines) =
    let filtered = (filterEmptyLines lines)
    in if Prelude.length filtered > 0
      then pre <> T.intercalate "\n" ((prettifyCode . tshow) <$> filtered) <> "\n" <> post
      else ""
    where (pre, post) = wildcardPrePost wild
  tshow (SpecialFlat s) = tshow s
  tshow (NewlineFlat) = "\n"
  tshow (SpaceFlat) = "\\space "

-- writeBlockLL (CommentLL t) = "CommentLL: " <> T.intercalate "\n" (tshow <$> t) <> "End comment."
-- writeBlockLL (HiddenCodeLL t) = "Hidden code: " <> T.intercalate "\n" (tshow <$> t) <> "End hidden code."
-- writeBlockLL (CodeLL t) = "CodeLL: " <> tshow t <> "\n"
-- writeBlockLL (TagLL t) = "Tag: " <> T.pack (show t) <> "\n"



myToken ::  (Show a) => (a -> Maybe b) -> Parsec [a] () b
myToken test = tokenPrim show incPos $ justIf test where
  incPos pos _ _ = incSourceColumn pos 1
  justIf test x = test x --   if (test x) then Just x else Nothing

codeLL = myToken f
  where f :: BlockLL -> Maybe Line
        f (CodeLL l) = Just l
        f _ = Nothing

-- commentLL :: Parsec [BlockLL] () Paragraph
-- commentLL = myToken f
--   where f :: BlockLL -> Maybe Paragraph
--         f (CommentLL ls) = case p of
--                             Right par -> Just par
--                             Left err -> Nothing -- trace ("Encountered error: " <> show err <> "\nwhile parsing a comment.") Nothing
--             where p = parse (pParagraph Nothing) "" ((T.unlines (getMainPart <$> ls)))
--                   getMainPart (Prefixed _ a) = a
--         f _ = Nothing




  -- we do not allow paragraphs with reset annotations
paragraphLL_OnlyContinuation :: Maybe Annotation -> Parsec [BlockLL] () Paragraph
paragraphLL_OnlyContinuation ann = myToken f
  where f :: BlockLL -> Maybe Paragraph
        f (CommentLL (FullComment mod ls)) =
          case mod of
            -- this is the case which we do not accept here,
            -- we only parse paragraphs which do not have the reset annotation
            (Just PM_ResetAnnotation) -> trace "### Backtracking because found ResetAnnotation." Nothing
            _ -> case p of
                      Right par -> Just par
                      Left err -> Nothing -- trace ("Encountered error: " <> show err <> "\nwhile parsing a comment.") Nothing
            -- where p = parse (pParagraph mod ann) "" ((T.unlines (getMainPart <$> ls)))
            where p = parse (pParagraph mod ann) "" ((T.intercalate "\n" (getMainPart <$> ls)))
                  getMainPart (Prefixed _ a) = a
        f _ = Nothing

paragraphLL :: Maybe Annotation -> Parsec [BlockLL] () Paragraph
paragraphLL ann = myToken f
  where f :: BlockLL -> Maybe Paragraph
        f (CommentLL (FullComment mod ls)) = case p of
                            -- Right par -> Just par
                            Right par -> trace ("parsed paragraph [" <> show mod <> "]\n" <> show par <> "\n----\n")(Just par)
                            Left err -> Nothing -- trace ("Encountered error: " <> show err <> "\nwhile parsing a comment.") Nothing
            -- where p = parse (pParagraph mod ann) "" ((T.unlines (getMainPart <$> ls)))
            where p = parse (pParagraph mod ann) "" ((T.intercalate "\n" (getMainPart <$> ls)))
                  getMainPart (Prefixed _ a) = a
        f _ = Nothing

hiddenCodeLL = myToken f
  where f :: BlockLL -> Maybe [Line]
        f (HiddenCodeLL l) = Just l
        f _ = Nothing
anyTagLL = myToken f
  where f :: BlockLL -> Maybe Tag
        f (TagLL t) = Just t
        f _ = Nothing
specialLL = myToken f
  where f :: BlockLL -> Maybe FullSpecial
        f (SpecialLL s) = Just s
        f _ = Nothing

tagLL s = myToken f
  where f :: BlockLL -> Maybe Tag
        f (TagLL t) = case s == t of
                        True -> Just s
                        False -> Nothing
        f _ = Nothing

type ParserLL = Parsec [BlockLL] ()

parseUntaggedBlockML :: Parsec [BlockLL] () BlockML
parseUntaggedBlockML = (CommentML <$> paragraphLL Nothing)
               <|> (HiddenCodeML <$> hiddenCodeLL)
               <|> (CodeML <$> (many1 codeLL))
               <|> (SpecialML <$> specialLL)
               -- <|> (TagML <$> anyTagLL)

parseUntaggedBlocksML :: Parsec [BlockLL] () [BlockML]
parseUntaggedBlocksML = many parseUntaggedBlockML

parseUntaggedBlockML_OnlyContinuation :: Parsec [BlockLL] () BlockML
parseUntaggedBlockML_OnlyContinuation = (CommentML <$> paragraphLL_OnlyContinuation Nothing)
               <|> (HiddenCodeML <$> hiddenCodeLL)
               <|> (CodeML <$> (many1 codeLL))
               <|> (SpecialML <$> specialLL)
               -- <|> (TagML <$> anyTagLL)

parseUntaggedBlocksML_OnlyContinuation :: Parsec [BlockLL] () [BlockML]
parseUntaggedBlocksML_OnlyContinuation = many parseUntaggedBlockML_OnlyContinuation

------------------------------------------------
-- Parsing comments


-- formatting
data CommentFormat =
  Italic | Bold
  deriving (Show)

delimiters :: CommentFormat -> (String,String)
delimiters Italic = ("/","/")
delimiters Bold = ("*","*")

latexFormat :: CommentFormat -> Text
latexFormat Italic = "\\textit"
latexFormat Bold = "\\textbf"

data CommentPart =
  CommentPart (Maybe CommentFormat) String
  | CommentPartCode AgdaTokens
  | LiteralTexCommentPart String
  | FootnoteCommentPart String
  deriving (Show)

data Wildcard =
  Inline | InlineHidden | Ownline Text
  deriving (Show)

data WildParagraph = WildParagraph Wildcard [CommentPart]
  deriving (Show)

data Paragraph =
  Split (Maybe ParagraphModality) [CommentPart] [WildParagraph]
  -- Simple [CommentPart]
  -- Split [CommentPart] Wildcard [CommentPart]
  deriving (Show)

class MapCommentPart a where
  mapcp :: (CommentPart -> CommentPart) -> a -> a

instance MapCommentPart CommentPart where
  mapcp f = f 

instance MapCommentPart WildParagraph where
  mapcp f (WildParagraph wc cps) = WildParagraph wc (f <$> cps)

instance MapCommentPart a => MapCommentPart [a] where
  mapcp f xs = mapcp f <$> xs

instance MapCommentPart Paragraph where
  mapcp f (Split mod cps wp) = Split mod (mapcp f cps) (mapcp f wp)

instance MapCommentPart ParagraphAnn where
  mapcp f (ParagraphAnn ann par) = ParagraphAnn ann (mapcp f par) 

instance MapCommentPart ParagraphFlat where
  mapcp f (ParagraphFlat cps) = ParagraphFlat (mapcp f cps)

data Annotation =
  EnumItem | ItemizeItem
  deriving (Show)

data ParagraphAnn =
  ParagraphAnn (Maybe Annotation) Paragraph
  deriving (Show)

data ParagraphFlat = ParagraphFlat [CommentPart]
  deriving (Show)

instance TShow CommentPart where
  tshow (CommentPart Nothing s) = T.pack s
  tshow (CommentPart (Just fmt) s) = latexFormat fmt <> "{" <> T.pack s <> "}"
  tshow (CommentPartCode at) = "$" <> tshow at <> "$"
  tshow (LiteralTexCommentPart s) = T.pack s
  tshow (FootnoteCommentPart s) = "\\footnote{" <> T.pack s <> "}"

instance TShow ParagraphFlat where
  tshow (ParagraphFlat parts) = T.concat (tshow <$> parts)

instance TShow WildParagraph where
  tshow (WildParagraph wild post) =  "[[wildcard!!]]" <> T.concat (tshow <$> post)

instance TShow Paragraph where
  -- tshow (Simple parts) = T.concat (tshow <$> parts)
  tshow (Split mod pre wildp) = modalityDoNewline mod <> T.concat (tshow <$> pre) <> tshow wildp -- "[[wildcard!!]]" <> T.concat (tshow <$> post)

modalityDoNewline :: Maybe ParagraphModality -> Text
modalityDoNewline (Just PM_NoNewline) = ""
modalityDoNewline _ = ""


specialChars :: [Char]
specialChars = "/*[]|$"

enumChars = "1234567890"
itemizeChars = "-"

annotationChars = enumChars <> itemizeChars

pCommentBase_NoParagraphBeginning :: Parsec Text () String
pCommentBase_NoParagraphBeginning = merge
                                  <$> satisfy (`notElem` (annotationChars <> specialChars))
                                  <*> (many (satisfy (`notElem` specialChars)))
  where merge a x = a : x

pCommentBase :: Parsec Text () String
pCommentBase = many1 (satisfy (`notElem` specialChars))

pCommentFormatted_Single :: CommentFormat -> Parsec Text () String
pCommentFormatted_Single form = try $ between (string dem1) (string dem2) pCommentBase
  where (dem1, dem2) = delimiters form

pCommentFormatted :: Parsec Text () CommentPart
pCommentFormatted = f Italic <|> f Bold
  where f fmt = CommentPart (Just fmt) <$> pCommentFormatted_Single fmt

pCommentCode :: Parsec Text () CommentPart
pCommentCode = CommentPartCode <$> between (char '|') (char '|') parseAgdaTokens

pLiteralTexComment :: Parsec Text () CommentPart
pLiteralTexComment = LiteralTexCommentPart <$> between (char '$') (char '$') (many1 (satisfy (`notElem` ("$" :: String))))

pFootnote :: Parsec Text () CommentPart
pFootnote = FootnoteCommentPart <$> between (string "[fn:: ") (char ']') (many1 (satisfy (`notElem` ("]" :: String))))

pCommentPart :: Parsec Text () CommentPart
pCommentPart = try (CommentPart Nothing <$> pCommentBase)
              <|> try pCommentFormatted
              <|> try pCommentCode
              <|> try pLiteralTexComment
              <|> try pFootnote

pCommentPart_NoParagraphBeginning :: Parsec Text () CommentPart
pCommentPart_NoParagraphBeginning = try (CommentPart Nothing <$> pCommentBase_NoParagraphBeginning)
                                    <|> try pCommentFormatted
                                    <|> try pCommentCode
                                    <|> try pLiteralTexComment
                                    <|> try pFootnote

pAnnotation :: Annotation -> Parsec Text () ()
pAnnotation EnumItem    = finalize <$> oneOf enumChars <*> string ". "
  where finalize _ _ = ()
pAnnotation ItemizeItem = finalize <$> string "- "
  where finalize _ = ()

pCommentPart_WithBeginning :: (Maybe Annotation) -> Parsec Text () CommentPart
pCommentPart_WithBeginning (Nothing)  = pCommentPart_NoParagraphBeginning
pCommentPart_WithBeginning (Just ann) = pAnnotation ann *> pCommentPart

pCommentParts_WithBeginning :: (Maybe Annotation) -> Parsec Text () [CommentPart]
pCommentParts_WithBeginning ann = (:) <$> pCommentPart_WithBeginning ann <*> many pCommentPart

pWildcard :: Parsec Text () Wildcard
pWildcard = try (const Inline <$> string "[..]")
          <|> try (const InlineHidden <$> string "[]")
          <|> try ((Ownline . T.pack) <$> (string "[..." *> many (satisfy (/= ']')) <* string "]"))

simple a = Split a []

pWildParagraph :: Parsec Text () WildParagraph
pWildParagraph = WildParagraph <$> pWildcard <*> many pCommentPart

pParagraph :: Maybe ParagraphModality -> Maybe Annotation -> Parsec Text () Paragraph
pParagraph mod ann = try (Split mod <$> pCommentParts_WithBeginning ann <*> many pWildParagraph <* eof)
                     <|> try (const (Split Nothing [] []) <$> eof)
-- pParagraph ann = try (simple <$> pCommentParts_WithBeginning ann <* eof)
--             <|> try (Split <$> pCommentParts_WithBeginning ann <*> pWildcard <*> many1 pCommentPart <* eof)

pParagraphAnn :: Maybe ParagraphModality -> Maybe Annotation -> Parsec Text () ParagraphAnn
pParagraphAnn mod ann = ParagraphAnn ann <$> pParagraph mod ann


-- data StrComment =
--   SingleFormatted FormComment
--   | Paragraph [StrComment]
--   | 

------------------------------------------------
-- Flattening blocks

comflat = CommentFlat . ParagraphFlat

makeNewline :: Maybe ParagraphModality -> [BlockFlat] -> [BlockFlat]
makeNewline (Just PM_NoNewline) xs = SpaceFlat : xs
makeNewline _ xs = NewlineFlat : xs


getFirstCharOfParts :: [CommentPart] -> Maybe Char
getFirstCharOfParts [] = Nothing
getFirstCharOfParts (x:xs) = f x
  where f :: CommentPart -> Maybe Char
        f (CommentPart _ []) = Nothing 
        f (CommentPart _ (x:xs)) = Just x 
        f _ = Nothing 

interleaveWildCode :: [WildParagraph] -> [Line] -> Either String [BlockFlat]
interleaveWildCode [] [] = return []
interleaveWildCode ((WildParagraph wild par) : ws) (c : cs) =
  do
    rest <- interleaveWildCode ws cs
    case (wild, getFirstCharOfParts par) of
      (Inline, Just ' ')  -> return (CodeFlat wild [c] : SpaceFlat : comflat par : rest)
      _                   -> return (CodeFlat wild [c] :             comflat par : rest)
interleaveWildCode (ws) [] = Left $ "Found wildcards:\n" <> show ws <> "\nbut no code is left."
interleaveWildCode [] (cs) = Right ([CodeFlat (Ownline "") cs])   -- Left $ "Found code:\n" <> show cs <> "\nbut no wildcards are left."

flattenBlocks :: [BlockML] -> Either String [BlockFlat]
flattenBlocks [] = Right []
flattenBlocks (CommentML (Split mod lines []) : xs) = adjoin <$> flattenBlocks xs
  where adjoin as = makeNewline mod (comflat lines : as)
flattenBlocks (CommentML (Split mod pre wild) : (CodeML code) : xs) = adjoin <$> interleaveWildCode wild code <*>  flattenBlocks xs
  where adjoin leaved as = makeNewline mod (((comflat pre) : leaved) <> as)
-- flattenBlocks (CommentML (Split pre wild post) : (CodeML code) : xs) = adjoin <$> flattenBlocks xs
--   where adjoin as = (comflat pre) : (CodeFlat wild code) : (comflat post) : NewlineFlat : as
flattenBlocks (CommentML (Split mod pre wild) : (HiddenCodeML code) : xs) =
  f <$> flattenBlocks (CommentML (Split mod pre wild) : xs) 
  where f x = (HiddenCodeFlat code) : x

flattenBlocks (CommentML (Split mod pre (x : xs)) : _) = Left $ "Expected code block after " <> show (Split mod pre (x : xs))

flattenBlocks (CodeML code : xs) = (CodeFlat (Ownline "") code :) <$> flattenBlocks xs
flattenBlocks (HiddenCodeML code : xs) = (HiddenCodeFlat code :) <$> flattenBlocks xs
flattenBlocks (SpecialML fs : xs) = (SpecialFlat fs :) <$> flattenBlocks xs

flattenLUAnn :: LogicalUnitAnn -> Either String (LogicalUnitAnn_ BlockFlat)
flattenLUAnn (LogicalUnitAnn (Split mod lines []) ys) = f <$> (flattenToplevel ys)
  where f zs = LogicalUnitAnn (Split mod lines []) zs
flattenLUAnn (LogicalUnitAnn (Split mod pre wild) (Toplevel (SimpleLU ((CodeML code1):codes):ys))) =
  do
    leaved <- interleaveWildCode wild code1
    flatcodes <- flattenBlocks codes
    flatys <- mapM flattenLU2 ys
    return (f leaved flatcodes flatys)
  where f leaved flatcodes flatys = LogicalUnitAnn (Split mod pre []) (Toplevel (SimpleLU (leaved <> flatcodes) : flatys))

flattenLUAnn (LogicalUnitAnn (Split mod pre wild) (Toplevel (SimpleLU ((HiddenCodeML code1):codes):ys))) =
  f <$> flattenLUAnn (LogicalUnitAnn (Split mod pre wild) (Toplevel (SimpleLU (codes):ys)))
  where f (LogicalUnitAnn s (Toplevel (SimpleLU val : rest))) = LogicalUnitAnn s (Toplevel (SimpleLU (HiddenCodeFlat code1 : val) : rest))
        f (a                                                ) = a
  -- where f flatcodes flatys = LogicalUnitAnn (Split pre []) (Toplevel (SimpleLU (CodeFlat wild code1 : (comflat post) : flatcodes) : flatys))
    -- adjoin as = (comflat pre) : (CodeFlat wild code) : (comflat post) : NewlineFlat : as
flattenLUAnn (LogicalUnitAnn (Split mod pre (x : xs)) (_)) = Left $ "Expected code block after " <> show (Split mod pre (x : xs))

-- flattenLU :: LogicalUnit -> Either String LogicalUnitFlat
-- flattenLU (TaggedLU t tag blocks) = TaggedLUFlat t tag <$> flattenBlocks blocks
-- flattenLU (FreestyleLU blocks) = FreestyleLUFlat <$> flattenBlocks blocks

flattenToplevel :: Toplevel BlockML -> Either String (Toplevel BlockFlat)
flattenToplevel (Toplevel a) = Toplevel <$> mapM flattenLU2 a

flattenLU2 :: LogicalUnit2 -> Either String (LogicalUnit2_ BlockFlat)
flattenLU2 (SimpleLU blocks) = SimpleLU <$> flattenBlocks blocks
flattenLU2 (TaggedLU2 text tag top) = TaggedLU2 text tag <$> flattenToplevel top
flattenLU2 (AnnotatedLU ann lus) = AnnotatedLU ann <$> mapM flattenLUAnn lus



------------------------------------------------
-- Into logical unit

-- theoremML

-- data TopLevel =
--   FreestyleTL [LogicalUnit2]

type LogicalUnitAnn = LogicalUnitAnn_ BlockML

data LogicalUnitAnn_ a = LogicalUnitAnn Paragraph (Toplevel a)
  deriving (Functor,Show)

type LogicalUnit2 = LogicalUnit2_ BlockML

data LogicalUnit2_ a =
    SimpleLU [a]
  | TaggedLU2 Text Tag (Toplevel a)
  | AnnotatedLU Annotation [LogicalUnitAnn_ a]
  deriving (Functor,Show)

data Toplevel a = Toplevel [LogicalUnit2_ a]
  deriving (Functor,Show)

instance MapCommentPart (LogicalUnitAnn_ a) where
  mapcp f (LogicalUnitAnn p tl) = LogicalUnitAnn (mapcp f p) tl

instance MapCommentPart (LogicalUnit2_ a) where
  mapcp f (SimpleLU as) = SimpleLU as
  mapcp f (TaggedLU2 t tag tops) = TaggedLU2 t tag (mapcp f tops)
  mapcp f (AnnotatedLU an las) = AnnotatedLU an (fmap (mapcp f) las)

instance MapCommentPart (Toplevel a) where
  mapcp f (Toplevel las) = Toplevel (fmap (mapcp f) las)


parseLU2_Tagged :: ParserLL LogicalUnit2
parseLU2_Tagged = try (TaggedLU2 "<<def name>>" <$> anyTagLL <*> parseToplevel <* tagLL End)

parseLU2_Annotated_Single :: Annotation -> ParserLL LogicalUnitAnn
parseLU2_Annotated_Single ann = try $ LogicalUnitAnn <$> paragraphLL (Just ann) <*> parseLU2_NotAnnotated_OnlyContinuation

parseLU2_Annotated_Single_OnlyContinuation :: Annotation -> ParserLL LogicalUnitAnn
parseLU2_Annotated_Single_OnlyContinuation ann = try $ LogicalUnitAnn <$> paragraphLL_OnlyContinuation (Just ann) <*> parseLU2_NotAnnotated_OnlyContinuation

parseLU2_Annotated :: ParserLL LogicalUnit2
parseLU2_Annotated = f EnumItem <|> f ItemizeItem
  where f ann = merge ann <$> (parseLU2_Annotated_Single ann) <*> many (parseLU2_Annotated_Single_OnlyContinuation ann)
        merge ann a as = AnnotatedLU ann (a : as)

parseLU2_NotAnnotated_OnlyContinuation :: ParserLL (Toplevel BlockML)
parseLU2_NotAnnotated_OnlyContinuation = Toplevel <$> many (parseLU2_Tagged <|> parseLU2_Simple_OnlyContinuation)

parseLU2_Simple_OnlyContinuation :: ParserLL LogicalUnit2
parseLU2_Simple_OnlyContinuation = try (SimpleLU <$> many1 parseUntaggedBlockML_OnlyContinuation)

parseLU2_Simple :: ParserLL LogicalUnit2
parseLU2_Simple = try (SimpleLU <$> many1 parseUntaggedBlockML)

-- parseToplevel_OnlyContinuation :: ParserLL (Toplevel BlockML)
-- parseToplevel_OnlyContinuation = Toplevel <$> many (try parseLU2_Tagged <|> try parseLU2_Annotated_OnlyContinuation <|> try parseLU2_Simple)

parseToplevel :: ParserLL (Toplevel BlockML)
parseToplevel = Toplevel <$> many (try parseLU2_Tagged <|> try parseLU2_Annotated <|> try parseLU2_Simple)



data LogicalUnit =
  TaggedLU Text Tag [BlockML]
  -- TheoremLU Text [BlockML]
  -- DefinitionLU Text [BlockML]
  | FreestyleLU [BlockML]
  deriving (Show)

data LogicalUnitFlat =
  TaggedLUFlat Text Tag [BlockFlat]
  | FreestyleLUFlat [BlockFlat]
  deriving (Show)


-- parseTheorem :: ParserLL LogicalUnit
-- parseTheorem = TheoremLU "Defname" <$> (tagLL Theorem *> parseUntaggedBlocksML <* tagLL End)

-- parseDefinition :: ParserLL LogicalUnit
-- parseDefinition = DefinitionLU "Defname" <$> (tagLL Definition *> parseUntaggedBlocksML <* tagLL End)

parseTagged :: ParserLL LogicalUnit
parseTagged = TaggedLU "Defname" <$> anyTagLL <*> (parseUntaggedBlocksML <* tagLL End)

parseFreestyle :: ParserLL LogicalUnit
parseFreestyle = FreestyleLU <$> (many1 parseUntaggedBlockML) --((:) <$> parseUntaggedBlockML <*> parseUntaggedBlocksML)

-- parseLU :: ParserLL [LogicalUnit]
-- parseLU = many (parseTagged <|> parseFreestyle)

tshow_escapeNewlines :: TShow a => [a] -> Text
tshow_escapeNewlines as = T.intercalate "%\n" (tshow <$> as)

tshow_concat :: TShow a => [a] -> Text
tshow_concat as = T.concat (tshow <$> as)

instance TShow LogicalUnitFlat where
  -- tshow (TheoremLU title blocks) = "\\begin{theorem}\n" <> tshow blocks <> "\n\\end{theorem}"
  -- tshow (DefinitionLU title blocks) = "\\begin{definition}\n" <> tshow blocks <> "\n\\end{definition}"
  tshow (TaggedLUFlat title tag blocks) = "\\begin{" <> tshow tag <> "}\n" <> tshow_escapeNewlines blocks <> "\n\\end{" <> tshow tag <>"}\n"
  tshow (FreestyleLUFlat blocks) = tshow_escapeNewlines blocks


instance TShow a => TShow (LogicalUnitAnn_ a) where
  tshow (LogicalUnitAnn par a) = "\\item " <> tshow par <> "%\n" <> tshow a

envForAnn :: Annotation -> (Text,Text)
envForAnn EnumItem = ("\\begin{enumerate}[itemsep=5pt, topsep=5pt, parsep=0pt, label=(\\roman*)]", "\\end{enumerate}")
envForAnn ItemizeItem = ("\\begin{itemize}[itemsep=5pt, topsep=5pt, parsep=0pt]","\\end{itemize}")

instance TShow a => TShow (LogicalUnit2_ a) where
  tshow (SimpleLU blocks) =  tshow_escapeNewlines blocks
  tshow (TaggedLU2 text tag lus) = "\\begin{" <> tshow tag <> "}\n" <> tshow lus <> "\n\\end{" <> tshow tag <>"}\n"
  tshow (AnnotatedLU ann lus) = pre <> "\n" <> tshow_escapeNewlines lus <> "\n" <> post <>"\n"
    where (pre,post) = envForAnn ann

instance TShow a => TShow (Toplevel a) where
  tshow (Toplevel lus) = tshow_escapeNewlines lus
  -- tshow (TaggedLUFlat title tag blocks) = "\\begin{" <> tshow tag <> "}\n" <> tshow_escapeNewlines blocks <> "\n\\end{" <> tshow tag <>"}\n"
  -- tshow (FreestyleLUFlat blocks) = tshow_escapeNewlines blocks


-- parseDefinition :: ParserLL LogicalUnit
-- parseDefinition = tagLL Theorem *> parseUntaggedBlocksML <* tagLL End



executeCodeCommands :: [SpecialCommand] -> Toplevel BlockFlat -> Toplevel BlockFlat
executeCodeCommands cmd top = mapcp f (fmap (mapcp f) top) 
  where f :: CommentPart -> CommentPart
        f (CommentPartCode toks) = CommentPartCode (processTerm cmd toks)
        f a = a


-- parseLogicalUnit :: [Block2] -> LogicalUnit
-- parseLogicalUnit = undefined

showleft :: Show a => Either a b -> Either String b
showleft (Left a) = Left (show a)
showleft (Right b) = Right b

doParseML :: [SpecialCommand] -> [BlockLL] -> Either String (Toplevel BlockFlat)
doParseML cmd blocks =
  let blocks2 = Prelude.filter (/= HiddenCommentLL) blocks

  in do lus <- showleft $ parse (parseToplevel <* eof) "" blocks2 
        traceM $ "#####################################\n before flattening:\n " <> show lus <> "\n#########################################\n"
        flats <- flattenToplevel lus
        let changedFlats = executeCodeCommands cmd flats
        return changedFlats


