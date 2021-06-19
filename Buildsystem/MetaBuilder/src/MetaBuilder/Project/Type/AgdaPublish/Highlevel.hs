{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module MetaBuilder.Project.Type.AgdaPublish.Highlevel where

import Prelude as P

import Debug.Trace

import Data.Text as T
import Data.Text.IO as TIO
-- import Control.Applicative
import Control.Monad

import Text.Parsec hiding (Line)

import qualified Data.List.Split as LS
import qualified Data.List as L



import Agda.Interaction.Highlighting.LaTeX.ExternalCall
import Agda.Interaction.Highlighting.LaTeX.Prettify
import Agda.Interaction.Highlighting.Precise

import MetaBuilder.Project.Type.AgdaPublish.Common
import MetaBuilder.Project.Type.AgdaPublish.Persistent

type Commands = [SpecialCommand]


myToken ::  (Show a) => (a -> Maybe b) -> Parsec [a] () b
myToken test = tokenPrim show incPos $ justIf test where
  incPos pos _ _ = incSourceColumn pos 1
  justIf test x = test x --   if (test x) then Just x else Nothing

data TokenContainer a = TokenContainer
  {
    original :: a,
    parsedToken :: TokenHL
  }
instance Show (TokenContainer a) where
  show (TokenContainer _ tok) = "TC{" <> show tok <> "}"

data IsImplicit = IsImplicit | NotImplicit
  deriving (Show)

data MultiTokenContainer a =
  SingleTC (TokenContainer a)
  | MultipleTC [MTC a]
  | WhitespaceTC (TokenContainer a)
  | RecordDef [(TokenContainer a)]
  | AllClause IsImplicit [MTC a]
  | UniverseClause (TokenContainer a) [MTC a]
  | UniverseLevelClause
  | ExponentialClause [MTC a]
  | SubscriptClause [MTC a]
  | ImplicitAssignmentClause (TC a) [MTC a]
  | SeperatorClause (TC a) Separator [MTC a]
  | LambdaClause (TC a) [MTC a] (TC a)
  | HiddenDelimiterClause [MTC a]
  | StructureOfClause [MTC a]
  deriving (Show)

-- SingleTC a = MultipleTC [a]

type TC a = TokenContainer a
type MTC a = MultiTokenContainer a


stringTC :: (TokenLike a, Show a) => Text -> Parsec [a] () (TC a)
stringTC str = myToken g
  where g :: TokenLike a => a -> Maybe (TC a)
        g tok = let res = parse anyTokenHL "<<source>>" (getTokenText tok)
              in case res of
                  Left e -> Nothing
                  Right x -> case tshow x == str of
                    True -> Just (TokenContainer tok x)
                    False -> Nothing

liftTC :: (TokenLike a, Show a) => Parsec Text () TokenHL -> Parsec [a] () (TC a)
liftTC parser = myToken g
  where g :: TokenLike a => a -> Maybe (TokenContainer a)
        g t = let res = parse parser "<<source>>" (getTokenText t)
              in case res of
                  Right x -> Just (TokenContainer t x)
                  Left e -> Nothing

anyTC :: (TokenLike a, Show a) => Parsec [a] () (TokenContainer a)
anyTC = liftTC tokenHL

-- parsing records
pRecordDefMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pRecordDefMTC = merge <$> stringTC "record" <*> stringTC " " <*> liftTC simpleNameTokenHL
  where merge a b c = RecordDef (a : b : c : [])

stringsTC :: (TokenLike a, Show a) => [Text] -> Parsec [a] () [TC a]
stringsTC [] = return []
stringsTC (x : xs) = (:) <$> stringTC x <*> stringsTC xs

pAllClauseMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pAllClauseMTC = AllClause IsImplicit <$> p
  where p = between (stringsTC ["∀","{"]) (stringTC "}") (many1 pIntraMTC) <* try (stringsTC [" ", "→", " "])
  -- where p = between (stringsTC ["∀","{"]) (stringTC "}") (many1 (liftTC pNoBracesHL)) <* try (stringsTC [" ", "→", " "])

pAllClauseExplicitMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pAllClauseExplicitMTC = AllClause NotImplicit <$> p
  where p = between (stringsTC ["∀","("]) (stringTC ")") (many1 pIntraMTC) <* try (stringsTC [" ", "→", " "])
  -- where p = between (stringsTC ["∀","("]) (stringTC ")") (many1 (liftTC pNoParensHL)) <* try (stringsTC [" ", "→", " "])

pUniverseClauseMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pUniverseClauseMTC =  UniverseClause <$> stringTC "𝒰" <*> (stringTC " " *> maybeParensedTC)
--  (try p1 <|> (pure <$> try p2))
  -- where p1 = stringTC " " *> between (stringTC "(") (stringTC ")") (many1 (liftTC pNoParensHL))
  --       p2 = stringTC " " *> (liftTC simpleNameTokenHL)

pImplicitAssignmentClauseMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pImplicitAssignmentClauseMTC = ImplicitAssignmentClause
  <$> (stringsTC [" ", "{"] *> liftTC (simpleNameTokenHL) <* stringsTC [" ", "=", " "])
  <*> (many1 pIntraMTC <* stringTC "}") 

spaceTermMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a) -> Parsec [a] () (MTC a)
spaceTermMTC p = p <* pWhitespaceMTC

spaceTermTC :: (TokenLike a, Show a) => Parsec [a] () (TC a) -> Parsec [a] () (TC a)
spaceTermTC p = p <* liftTC pWhitespaceHL

pLambdaClauseMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pLambdaClauseMTC = merge <$> spaceTermTC (stringTC "λ")
                         <*> (many1 (spaceTermMTC (MultipleTC <$> maybeParensedTC)))
                        --  <*> many1 (try (spaceTermTC (liftTC (try simpleNameTokenHL))))
                         <*> stringTC ("→")
  where merge lam vars arr = LambdaClause lam vars arr


maybeParensedTC :: (TokenLike a, Show a) => Parsec [a] () [MTC a]
maybeParensedTC = (try $ between (stringTC "(") (stringTC ")") (many1 (pIntraMTC)))
                <|> (try (return <$> SingleTC <$> liftTC (simpleNameTokenHL)))

pExponentialClauseMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pExponentialClauseMTC = ExponentialClause <$> p
  where p = stringsTC [" ", "^", " "] *> maybeParensedTC

pSubscriptClauseMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pSubscriptClauseMTC = SubscriptClause <$> p
  where p = stringsTC [" ", "⌄", " "] *> maybeParensedTC

pAnyMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pAnyMTC = SingleTC <$> anyTC

pWhitespaceMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pWhitespaceMTC = WhitespaceTC <$> (liftTC pWhitespaceHL)

pIntraMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pIntraMTC = try pUniverseClauseMTC
      <|> try pStructureAccessMTC
      <|> try pStructureOfMTC
      <|> try pUniverseLevel_withArrow_MTC
      <|> try pUniverseLevelMTC
      <|> try pExponentialClauseMTC
      <|> try pSubscriptClauseMTC
      <|> try (SingleTC <$> liftTC pNoParensBracesHL)

-- parsing ⟨ 𝒞 ⟩
pStructureAccessMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pStructureAccessMTC = f <$> try (between (stringTC "⟨") (stringTC "⟩") (many1 pIntraMTC))
  where f t = HiddenDelimiterClause t 

-- parsing ` F `
pCastMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pCastMTC = f <$> try (between (stringTC "`") (stringTC "`") (many1 pIntraMTC))
  where f t = HiddenDelimiterClause t 

-- parsing {{of X}}
pStructureOfMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pStructureOfMTC = f <$> try (between (stringsTC ["⦃", "of", " "]) (stringTC "⦄") (many1 pIntraMTC))
  where f t = StructureOfClause t

pUniverseLevel :: (TokenLike a, Show a) => Parsec [a] () (TC a)
pUniverseLevel = stringTC "𝑖"
                <|> stringTC "𝑗"
                <|> stringTC "𝑘"
                <|> stringTC "𝑙"

pUniverseLevelMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pUniverseLevelMTC = (f <$> try (between (stringTC "(") (stringTC ")") (pUniverseLevel *> many1 pIntraMTC)))
                    <|> (f <$> pUniverseLevel)
  where f t = UniverseLevelClause 


pUniverseLevel_withArrow_MTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pUniverseLevel_withArrow_MTC = (f <$> try (between (stringTC "(") (spaceTermTC (stringTC ")") *> stringTC "→") (pUniverseLevel *> many1 pIntraMTC)))
                    <|> (f <$> pUniverseLevel)
  where f t = UniverseLevelClause 

pMTC :: (TokenLike a, Show a) => Parsec [a] () (MTC a)
pMTC = try pRecordDefMTC
      <|> try pAllClauseMTC
      <|> try pAllClauseExplicitMTC
      <|> try pStructureAccessMTC
      <|> try pCastMTC
      <|> try pStructureOfMTC
      <|> try pUniverseClauseMTC
      <|> try pUniverseLevel_withArrow_MTC
      <|> try pUniverseLevelMTC
      <|> try pExponentialClauseMTC
      <|> try pSubscriptClauseMTC
      <|> try pImplicitAssignmentClauseMTC
      <|> try pLambdaClauseMTC
      <|> try pWhitespaceMTC
      <|> try pAnyMTC


data Separator =
  SepSI -- Semantic Instance
  | SepSA -- Semantic Annotation
  | SepMF -- Module Field
  deriving (Show, Eq)

data TokenHL =
   QualifedHL Separator String [TokenHL]
  --  | AnyHL String
   | AnyHL String
   deriving (Show)


-- Parse qualified names
qualifiedNameTokenHL_Single :: Separator -> [Separator] -> Parsec Text () TokenHL
qualifiedNameTokenHL_Single sep [] = merge <$> (singleName) <*> many1 (pSep *> (AnyHL <$> singleName))
  where pSep = string (T.unpack (tshow sep))
        merge a as = QualifedHL sep (a) (as)
qualifiedNameTokenHL_Single sep (y:ys) = merge <$> (singleName) <*> many1 (pSep *> (qualifiedNameTokenHL (y:ys) <|> (AnyHL <$> singleName)))
  where pSep = string (T.unpack (tshow sep))
        merge a as = QualifedHL sep (a) (as)

qualifiedNameTokenHL_Impl :: [Separator] -> [Separator] -> Parsec Text () TokenHL
qualifiedNameTokenHL_Impl [] _ = undefined
qualifiedNameTokenHL_Impl [x] ys = try (qualifiedNameTokenHL_Single x ys)
qualifiedNameTokenHL_Impl (x:xs) ys = try (qualifiedNameTokenHL_Single x (xs <> ys))
                                <|> qualifiedNameTokenHL_Impl xs (x : ys)

qualifiedNameTokenHL :: [Separator] -> Parsec Text () TokenHL
qualifiedNameTokenHL seps = qualifiedNameTokenHL_Impl seps []

-- seps = try (qualifiedNameTokenHL_Single SepSI (P.filter (/= SepSI) seps))
--                         <|> try (qualifiedNameTokenHL_Single SepSA (P.filter (/= SepSA) seps))
--                         <|> try (qualifiedNameTokenHL_Single SepMF (P.filter (/= SepMF) seps))
  -- where onAll = Prelude.foldr (\sep a -> a <|> try (qualifiedNameTokenHL_Single sep [s | s <- seps ])) 

-- parse simple names
simpleNameTokenHL :: Parsec Text () TokenHL
simpleNameTokenHL = AnyHL <$> singleName

-- parse record headings

-- parse the rest of names
anyTokenHL :: Parsec Text () TokenHL
anyTokenHL = AnyHL <$> (many anyChar <* eof)

notWhitespaceHL :: Parsec Text () TokenHL
notWhitespaceHL = AnyHL <$> (many (noneOf [' ', '\n']) <* eof)

specialSymbols = [' ', '\n', '\t', '∀', '(', ')', '{', '}', '@']

singleName :: Parsec Text () String
singleName = try $ many1 (noneOf $ [':', '-', '.', '→'] <> specialSymbols)

tokenHL :: Parsec Text () TokenHL
tokenHL = try (qualifiedNameTokenHL [SepSI, SepSA, SepMF]) <|> try simpleNameTokenHL <|> try notWhitespaceHL

pNoBracesHL :: Parsec Text () TokenHL
pNoBracesHL = try $ AnyHL <$> many1 (noneOf $ ['{', '}'])

pNoParensHL :: Parsec Text () TokenHL
pNoParensHL = try $ AnyHL <$> many1 (noneOf $ ['(', ')'])

pNoParensBracesHL :: Parsec Text () TokenHL
pNoParensBracesHL = try (qualifiedNameTokenHL [SepSI, SepSA, SepMF]) <|> (try $ AnyHL <$> many1 (noneOf $ "(){}⟨⟩`⦃⦄"))

pWhitespaceHL :: Parsec Text () TokenHL
pWhitespaceHL = try $ AnyHL <$> many1 (char ' ' <|> char '\n')


---------------------------------------------------------------------
-- Generating tokens back from parsed token containers

instance TShow Separator where
  tshow SepSA = "-"
  tshow SepSI = ":"
  tshow SepMF = "."

instance TShow TokenHL where
  -- tshow :: TokenHL -> Text
  tshow (QualifedHL sep main toks) = T.pack main <> generateQualifedHL sep (tshow <$> toks)
  -- tshow (AnyHL t) = T.pack t
  tshow (AnyHL t) = T.pack t


generateQualifedHL :: Separator -> [Text] -> Text
generateQualifedHL sep [] = ""
generateQualifedHL sep (x : []) = x
generateQualifedHL sep (x : xs) = x <> tshow sep <> generateQualifedHL sep xs


updateToken :: TokenLike a => a -> TokenHL -> a
updateToken a t = setTokenText a (tshow t)

formatAspect :: Format -> Maybe Aspect
formatAspect (Format fs su) = Just (MetabuilderAspect (from_fs fs <> from_su su))
  where from_fs :: FontStyle -> Text
        from_fs = T.pack . show 
        from_su :: IsSubscript -> Text
        from_su IsSubscript = "Subscript"
        from_su NotSubscript = ""

concatM :: Monad m => [a -> m a] -> a -> m a 
concatM [] = return 
concatM (f : fs) = f >=> (concatM fs)


additionalWhiteSpaceTC :: TokenLike a => String -> String -> [TC a]
additionalWhiteSpaceTC r t =
  let n = (P.length t + 1) - P.length r -- +1 because removed a separator
  in case n > 0 of
      True -> let white = P.concat (P.take n (repeat (descape " "))) in [TokenContainer (makePlainToken Nothing "") (AnyHL white) ]
      -- True -> let white = P.concat (P.take n (repeat " ")) in [TokenContainer (makePlainToken Nothing "") (AnyHL white) ]
      False -> []

fillAdditionalWhitespace :: Int -> String -> String
fillAdditionalWhitespace n1 s2 =
  let n = n1 - (P.length s2)
  in case n > 0 of
      True  -> let white = P.concat (P.take n (repeat (descape " "))) in s2 <> white
      False -> s2


type SepMTC a = (TC a, Separator, [MTC a])

executeCommand_Simple :: TokenLike a => SpecialCommand -> TC a -> TC a
-- -- Processing of raw occurences of semantic categories
executeCommand_Simple (NotationSC fmt r t) (TokenContainer a x) | tshow x == T.pack t =
   TokenContainer (makePlainToken (formatAspect (Format (fmt) NotSubscript)) "") (AnyHL r)
executeCommand_Simple (NotationRewrite s1 s2) (TokenContainer a x) | tshow x == T.pack s1 =
   TokenContainer a (AnyHL (fillAdditionalWhitespace (P.length s1) (descape s2)))
executeCommand_Simple cmd a = a


executeCommand_Separator :: TokenLike a => SpecialCommand -> SepMTC a -> MTC a
-- Processing names like "Category:Set"
executeCommand_Separator (NotationSC_Short fmt r t) (TokenContainer a x, SepSI, [y]) | tshow x == T.pack t =
   MultipleTC ([ y
   , SingleTC $ TokenContainer (makePlainToken (formatAspect (Format (fmt) IsSubscript)) "") (AnyHL r)
   ] <> (SingleTC <$> additionalWhiteSpaceTC r t))

-- -- Processing fields like "Category.Hom"
executeCommand_Separator (NotationSC fmt r t) (TokenContainer a x, SepMF, [y]) | tshow x == T.pack t =
  MultipleTC (
   [ y ] <> (SingleTC <$> additionalWhiteSpaceTC "" t))
   
-- -- Processing function names like "return-Maybe"
executeCommand_Separator (NotationSA annotatable) (TokenContainer a x, SepSA, [SingleTC y]) = -- a | tshow x == T.pack annotatable =
   MultipleTC ( [ SingleTC (TokenContainer a x)
   , SingleTC $ TokenContainer (makePlainToken (formatAspect (Format Sans IsSubscript) ) "") (parsedToken y)
   ] <> (SingleTC <$> additionalWhiteSpaceTC "" "") -- NOTE: here we want only a single whitespace added (because we remove the '-')
   )
executeCommand_Separator (NotationSA annotatable) (TokenContainer a x, SepSA, [SingleTC y, SingleTC z]) = -- a | tshow x == T.pack annotatable =
   MultipleTC ( [ SingleTC (TokenContainer a x)
   , SingleTC $ TokenContainer (makePlainToken (formatAspect (Format Sans IsSubscript) ) "") (retTok)
   ] <> (SingleTC <$> additionalWhiteSpaceTC "" "") -- NOTE: here we want only a single whitespace added (because we remove the '-')
   )
   where yt = (T.unpack $ tshow (parsedToken y))
         zt = (T.unpack $ tshow (parsedToken z))
         retTok = AnyHL (yt <> "," <> zt)
-- A hack to get multi containers to work (but definitely destroys whitespace counting)
-- executeCommand_Separator (NotationSA annotatable) (TokenContainer a x, SepSA, [MultipleTC tcs]) =
-- -- executeCommand_Separator (NotationSA annotatable) (TokenContainer a x, SepSA, [SeperatorClause sc1 sc2 sc3]) =
--   MultipleTC ( [
--     SingleTC (TokenContainer a x),
--     -- SingleTC $ TokenContainer (makePlainToken Nothing "") (AnyHL $ descape "_"),
--     SingleTC $ TokenContainer (makePlainToken Nothing "") (AnyHL $ descape "_{"),
--     -- SeperatorClause sc1 sc2 sc3,
--     MultipleTC tcs,
--     SingleTC $ TokenContainer (makePlainToken Nothing "") (AnyHL $ descape "}")
--   ])

executeCommand_Separator cmd (a, sep, mtcs) = SeperatorClause a sep (mtcs >>= executeCommand_MTC cmd)

executeCommand :: TokenLike a => SpecialCommand -> TokenContainer a -> [TokenContainer a]
executeCommand cmd = pure . executeCommand_Simple cmd
-- Processing names like "Category:Set"
-- executeCommand (NotationSC_Short fmt replacement target) (TokenContainer a (QualifedHL SepSI x (y : []))) =
--    case target == x of
--      True -> [ (TokenContainer a y)
--              , TokenContainer (makePlainToken (formatAspect (Format (fmt) IsSubscript)) "") (AnyHL replacement)
--              ]
--      False -> [TokenContainer a (QualifedHL SepSI x (y : []))]
-- -- Processing fields like "Category.Hom"
-- executeCommand (NotationSC fmt replacement target) (TokenContainer a (QualifedHL SepMF x (y : []))) =
--    case target == x of
--      True -> [ TokenContainer a y -- in this case we simply hide the qualification
--              ]
--      False -> [TokenContainer a (QualifedHL SepMF x (y : []))]
-- -- Processing function names like "return-Maybe"
-- executeCommand (NotationSA annotatable) (TokenContainer a (QualifedHL SepSA x (y : []))) =
--    case annotatable == x of
--      True -> [ TokenContainer a (AnyHL x)
--              , TokenContainer (makePlainToken (formatAspect (Format Sans IsSubscript) ) "") (y)
--              ]
--      False -> [TokenContainer a (QualifedHL SepSA x (y : []))]
-- -- Processing of raw occurences of semantic categories
-- executeCommand (NotationSC fmt replacement target) (TokenContainer a (AnyHL x)) =
--    case target == x of
--      True -> [ TokenContainer (makePlainToken (formatAspect (Format (fmt) NotSubscript)) "") (AnyHL replacement)
--              ]
--      False -> [TokenContainer a (AnyHL x)]
-- -- Ignoring all other tokencontainers
-- executeCommand (_) (tc) = [tc]

executeCommand_MTC :: TokenLike a => SpecialCommand -> MTC a -> [MTC a]
executeCommand_MTC (NotationSC _ r t)         (RecordDef tc) = [RecordDef (tc >>= executeCommand (NotationSC MathBF r t))]
executeCommand_MTC (NotationSC_Short fmt r t) (RecordDef tc) = [RecordDef (tc >>= executeCommand (NotationSC_Short fmt r t))]
executeCommand_MTC _                          (RecordDef tc) = [RecordDef tc]
executeCommand_MTC cmd (SingleTC tc) = SingleTC <$> executeCommand cmd tc
executeCommand_MTC cmd (MultipleTC tc) = [MultipleTC (executeCommand_MTC cmd =<< tc)]
executeCommand_MTC cmd (WhitespaceTC tc) = [WhitespaceTC tc]
executeCommand_MTC cmd (AllClause i tcs) = [AllClause i (tcs >>= executeCommand_MTC cmd)]
executeCommand_MTC cmd (UniverseClause uni tcs) = [UniverseClause uni (tcs >>= executeCommand_MTC cmd)]
executeCommand_MTC cmd (ExponentialClause tcs) = [ExponentialClause (tcs >>= executeCommand_MTC cmd)]
executeCommand_MTC cmd (SubscriptClause tcs) = [SubscriptClause (tcs >>= executeCommand_MTC cmd)]
executeCommand_MTC cmd (ImplicitAssignmentClause tc tcs) = [ImplicitAssignmentClause tc (tcs >>= executeCommand_MTC cmd)]
executeCommand_MTC cmd (SeperatorClause tc sep mtcs) = [executeCommand_Separator cmd (tc, sep, mtcs)]
executeCommand_MTC cmd (LambdaClause lam vars arr) = [LambdaClause lam (executeCommand_MTC cmd =<< vars) arr]
executeCommand_MTC cmd (HiddenDelimiterClause tcs) = [HiddenDelimiterClause (executeCommand_MTC cmd =<< tcs)]
executeCommand_MTC cmd (StructureOfClause tcs) = [StructureOfClause (executeCommand_MTC cmd =<< tcs)]
executeCommand_MTC cmd (UniverseLevelClause) = [UniverseLevelClause]


-- QualifedHL :: TokenLike a => Commands -> a -> [String] -> [a]
-- QualifedHL cmd a [] = [a]
-- QualifedHL cmd a (x : y : []) = [updateToken a (AnyHL y), makePlainToken (Just (MetabuilderAspect "RomanSubscript")) (T.pack x)]
-- QualifedHL cmd a r = [a]


-- generateToken :: TokenLike a => Commands -> a -> TokenHL -> [a]
-- generateToken cmd a (QualifedHL xs) = QualifedHL cmd a xs
-- generateToken cmd a (r) = [updateToken a r]

data KillCommand = KillSpaceRight | KillSpaceLeft

generateToken :: TokenLike a => TokenContainer a -> Either KillCommand a
generateToken (TokenContainer a t) = Right (updateToken a t)

-- wrapBraces :: TokenLike a => [a] -> [a]
-- wrapBraces = [makePlainToken Nothing (T.pack (descape "{"))]

generateToken_MTC :: TokenLike a => MTC a -> [Either KillCommand a]
generateToken_MTC (SingleTC tc) = [generateToken tc]
generateToken_MTC (MultipleTC tc) = generateToken_MTC =<< tc
generateToken_MTC (WhitespaceTC tc) = [generateToken tc]
generateToken_MTC (RecordDef tc) = generateToken <$> tc
generateToken_MTC (AllClause implicit tcs) = [Right $ makePlainToken Nothing (T.pack l)]
                                    <> (generateToken_MTC =<< tcs)
                                    <> [Right $ makePlainToken Nothing (T.pack r)]
  where l = descape "{\\color{AgdaBound}\\prod_{" <> extra_l implicit  -- [char_Backslash] <> -- "prod" <> [char_Underscore, char_BraceOpen, '{']
        r = extra_r implicit <> descape "}}"

        extra_l IsImplicit  = "{"
        extra_l NotImplicit = descape "\\ "
        extra_r IsImplicit  = "}"
        extra_r NotImplicit = descape "\\ "

generateToken_MTC (UniverseClause uni tcs) = [generateToken uni]
  --                                            <> [Right $ makePlainToken Nothing (T.pack l)]
  --                                            <> (generateToken_MTC =<< tcs)
  --                                            <> [Right $ makePlainToken Nothing (T.pack r)]
  -- where l = descape "_{"
  --       r = descape "}"
generateToken_MTC (ExponentialClause tcs) = [Right $ makePlainToken Nothing (T.pack l)]
                                             <> (generateToken_MTC =<< tcs)
                                             <> [Right $ makePlainToken Nothing (T.pack r)]
  where l = descape "^{"
        r = descape "}"
generateToken_MTC (SubscriptClause tcs) = [Right $ makePlainToken Nothing (T.pack l)]
                                             <> (generateToken_MTC =<< tcs)
                                             <> [Right $ makePlainToken Nothing (T.pack r)]
  where l = descape "_{"
        r = descape "}"
generateToken_MTC (ImplicitAssignmentClause target tcs) = 
    [Right $ makePlainToken Nothing (T.pack l)]
    <> [generateToken target]
    <> [Right $ makePlainToken Nothing (T.pack m)]
    <> (generateToken_MTC =<< tcs)
    <> [Right $ makePlainToken Nothing (T.pack r)]
  where l = descape "{}_{" <> "{"
        m = " := "
        r = "}" <> descape "}"
generateToken_MTC (SeperatorClause main sep mtcs) =
  [generateToken main, sepToken] <> L.intercalate [sepToken] (generateToken_MTC <$> mtcs)
  where sepTC = main {parsedToken = AnyHL (T.unpack $ tshow sep)}
        sepToken = generateToken sepTC
generateToken_MTC (LambdaClause lam vars (TokenContainer arr _)) =
  [generateToken lam, Right sepToken] <> L.intercalate [Right sepToken] (generateToken_MTC <$> vars) <> [Right sepToken, Right arrToken]
  where
        sepToken = makePlainToken Nothing " "
        arrToken = updateToken arr (AnyHL (descape "\\mapsto"))
generateToken_MTC (HiddenDelimiterClause mtcs) = [Left KillSpaceRight] <> (generateToken_MTC =<< mtcs) <> [Left KillSpaceLeft]
generateToken_MTC (StructureOfClause mtcs) =
    [Left KillSpaceLeft]
    <> [Right $ makePlainToken Nothing (T.pack l)]
    <> (generateToken_MTC =<< mtcs)
    <> [Right $ makePlainToken Nothing (T.pack r)]
  -- where l = descape "\\NegAgdaSpace{}{}_{"
  where l = descape "{}_{"
        r = descape "}"
generateToken_MTC (UniverseLevelClause) = [Left KillSpaceLeft]

isWhitespace :: TokenLike a => a -> Bool
isWhitespace a = T.all (== ' ') (getTokenText a)


isEscapedWhitespace :: TokenLike a => a -> Bool
isEscapedWhitespace a = T.all (== char_Whitespace) (getTokenText a)

killSpace :: TokenLike a => [Either KillCommand a] -> [a]
killSpace [] = []
killSpace (Right a : []) = [a]
killSpace (Left  _ : []) = []
-- killSpace (Left KillSpaceRight : Right w : xs)                  = killSpace xs -- <<= WRONG
killSpace (Left KillSpaceRight : Right w : xs) | isWhitespace w = killSpace xs
killSpace (Left KillSpaceRight : Right w : xs) | otherwise      = killSpace (Right w : xs)
killSpace (Left KillSpaceLeft  : Right w : xs)                  = killSpace (Right w : xs)
-- killSpace (Right w : Left KillSpaceLeft : xs)  | otherwise      = killSpace xs -- <<= WRONG
killSpace (Right w : Left KillSpaceLeft : xs)  | isWhitespace w = killSpace xs
killSpace (Right w : Left KillSpaceLeft : xs)  | otherwise      = w : killSpace xs
killSpace (Right w : Left KillSpaceRight : xs)                  = w : killSpace (Left KillSpaceRight : xs)
killSpace (Left a : Left b : xs)                                = killSpace (Left b : xs)
killSpace (Right w : Right v : xs)                              = w : killSpace (Right v : xs)
-- killSpace (Right w : Left v : xs)                              = w : killSpace (Right v : xs)

regenerateTokens_MTC :: TokenLike a => Commands -> MTC a -> [Either KillCommand a]
regenerateTokens_MTC cmd container =
  let containers = concatM (executeCommand_MTC <$> cmd) container
      res = trace ("\nAfter commands: " <> show containers) containers
  in (res >>= generateToken_MTC)

-- regenerateTokens :: TokenLike a => Commands -> TokenContainer a -> [a]
-- regenerateTokens cmd container =
--   let containers = concatM (executeCommand <$> cmd) container
--   in generateToken <$> containers

tokReplacements =
  [ -- ("𝑖", descape "i")
    -- ("𝑖𝑖", descape "\\dot{i}")
    -- ("𝑖𝑖𝑖", descape "\\ddot{i}")
    ("､", descape ",")
  , ("=?=", descape "{\\times_{?}}")
  ]

tryReplace :: Eq b => [(b, b)] -> (a -> Maybe b) -> (b -> a) -> a -> a
tryReplace [] _ _ x = x
tryReplace ((t,r) : bs) g h x | g x == Just t = h r
tryReplace ((t,r) : bs) g h x = tryReplace bs g h x 

  
processToken :: TokenLike a => TC a -> TC a
processToken (TokenContainer orig (AnyHL "=")) = TokenContainer orig (AnyHL ":=")
processToken (TokenContainer orig (AnyHL "→")) = TokenContainer orig (AnyHL (descape "\\operatorname{→}"))
processToken (TokenContainer orig (AnyHL "field")) = TokenContainer (makePlainToken Nothing "") (AnyHL (descape "     "))
processToken x = tryReplace tokReplacements g h x
  where g (TokenContainer orig (AnyHL tok)) = Just tok
        g _ = Nothing
        h tok = TokenContainer (makePlainToken Nothing "") (AnyHL (descape tok))

changeTC :: TokenLike a => (TC a -> TC a) -> MTC a -> MTC a
changeTC f (SingleTC tc)      = SingleTC (f tc)
changeTC f (MultipleTC mtc)   = MultipleTC (changeTC f <$> mtc)
changeTC f (WhitespaceTC tc)  = WhitespaceTC (f tc)
changeTC f (RecordDef a)      = RecordDef (f <$> a)
changeTC f (AllClause i mtcs)  = AllClause i (changeTC f <$> mtcs)
changeTC f (UniverseClause tc mtcs)           = UniverseClause (f tc) (changeTC f <$> mtcs)     
changeTC f (ExponentialClause mtcs)          = ExponentialClause (changeTC f <$> mtcs) 
changeTC f (SubscriptClause mtcs)            = SubscriptClause (changeTC f <$> mtcs)
changeTC f (ImplicitAssignmentClause tc mtcs) = ImplicitAssignmentClause (f tc) (changeTC f <$> mtcs)
changeTC f (SeperatorClause tc sep mtcs) = SeperatorClause (f tc) sep (changeTC f <$> mtcs)
changeTC f (LambdaClause tc mtcs tc2) = LambdaClause (f tc) (changeTC f <$> mtcs) (f tc2)
changeTC f (HiddenDelimiterClause mtcs) = HiddenDelimiterClause (changeTC f <$> mtcs)
changeTC f (StructureOfClause mtcs) = StructureOfClause (changeTC f <$> mtcs)
changeTC f (UniverseLevelClause) = UniverseLevelClause

processToken_MTC :: TokenLike a => MTC a -> MTC a
processToken_MTC = changeTC processToken
-- processToken_MTC (SingleTC (TokenContainer orig (AnyHL "{{"))) = SingleTC (TokenContainer orig (AnyHL "⦃"))
-- processToken_MTC (SingleTC (TokenContainer orig (AnyHL "}}"))) = SingleTC (TokenContainer orig (AnyHL "⦄"))

embedQualifiedIntoMTC_MTC :: TokenLike a => MTC a -> MTC a
embedQualifiedIntoMTC_MTC (SingleTC tc) = ((embedQualifiedIntoMTC) tc)
embedQualifiedIntoMTC_MTC (MultipleTC tc) = MultipleTC $ (embedQualifiedIntoMTC_MTC <$> tc)
embedQualifiedIntoMTC_MTC (HiddenDelimiterClause mtcs) = HiddenDelimiterClause $ embedQualifiedIntoMTC_MTC <$> mtcs
embedQualifiedIntoMTC_MTC a = a

-- | Break down TCs in which a QualifiedHL is inside into an actual MTC with constructor SeparatorClause
--   i.e., lift the qualified name given by QualifiedHL to a qualified MTC given by SeparatorClause
embedQualifiedIntoMTC :: TokenLike a => TC a -> (MTC a)
embedQualifiedIntoMTC ((TokenContainer a (QualifedHL sep main xs)))
   = (SeperatorClause (TokenContainer a (AnyHL main)) sep (f <$> xs))
   where f tok = embedQualifiedIntoMTC ((TokenContainer a tok))
embedQualifiedIntoMTC tc = SingleTC tc

---------------------------------------------------------------------
-- Replace {{,}} by short ones
replaceToken :: TokenLike a => a -> a
replaceToken a | getTokenText a == "{{" = setTokenText a "⦃"
replaceToken a | getTokenText a == "}}" = setTokenText a "⦄"
replaceToken a = a

---------------------------------------------------------------------
-- Splitting tokens with (,),{,}

splitToken :: TokenLike a => a -> [a]
splitToken a =
  let t = T.unpack $ getTokenText a
      t2 = LS.split (LS.dropInitBlank . LS.dropFinalBlank . LS.dropInnerBlanks . LS.oneOf $ "{()}⦃⦄") t
      -- t2 = LS.split (LS.dropInitBlank . LS.dropFinalBlank . LS.dropInnerBlanks . LS.oneOf $ "{()}_⦃⦄") t
      t3 = T.pack <$> t2
      f x = setTokenText a x
  in f <$> t3

---------------------------------------------------------------------
-- Remove trailing whitespace
removeTrailingWS :: TokenLike a => [a] -> [a]
removeTrailingWS xs = P.filter (not . isEscapedWhitespace) xs
  --  P.reverse (f (P.reverse xs))
  -- where f [] = []
  --       f (x : xs) | isWhitespace (original x) = f xs
  --       f (x : xs) | otherwise                 = x : f xs

---------------------------------------------------------------------
-- Parsing and generating

intoTC :: TokenLike a => a -> TokenContainer a
intoTC a = TokenContainer a (AnyHL . T.unpack $ getTokenText a)


intoMTC :: TokenLike a => a -> MTC a
intoMTC = SingleTC . intoTC

parseAndGenerate :: (Show a, TokenLike a) => [SpecialCommand] -> [a] -> [a]
parseAndGenerate cmd input0 =
    let input = (splitToken . replaceToken) =<< input0
        res = parse (many pMTC) "<<input>>" input
        res2 = case res of
                Right x -> trace ("\nBefore processing:\n" <> show x) x
                Left err -> trace ("Error in parsing tokens: " <> show err) (intoMTC <$> input )
        res3 = embedQualifiedIntoMTC_MTC . processToken_MTC <$> res2
        res4 = trace ("\n\nAfter processing:\n" <> show res3) res3
        res5 = killSpace $ res4 >>= regenerateTokens_MTC cmd
    in res5


-- parseAndGenerateNoTrailingWS :: (Show a, TokenLike a) => [SpecialCommand] -> [a] -> [a]
-- parseAndGenerateNoTrailingWS cmd input0 =
--     let input = (splitToken . replaceToken) =<< input0
--         res = parse (many pMTC) "<<input>>" input
--         res2 = case res of
--                 Right x -> trace ("\nBefore processing:\n" <> show x) x
--                 Left err -> trace ("Error in parsing tokens: " <> show err) (intoMTC <$> input )
--         res3 = embedQualifiedIntoMTC_MTC . processToken_MTC <$> res2
--         res4 = trace ("\n\nAfter processing:\n" <> show res3) res3
--         res5 = killSpace $ (removeTrailingWS res4) >>= regenerateTokens_MTC cmd
--     in res5
