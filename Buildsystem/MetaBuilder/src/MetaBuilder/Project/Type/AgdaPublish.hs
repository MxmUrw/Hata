{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module MetaBuilder.Project.Type.AgdaPublish where

import Paths_MetaBuilder
import MetaBuilder.Project.Type.AgdaPublish.Lowlevel
import MetaBuilder.Project.Type.AgdaPublish.Midlevel
import MetaBuilder.Project.Type.AgdaPublish.Persistent
import MetaBuilder.Project.Type.AgdaPublish.Common

import Data.Text as T
import Data.Text.IO as TIO

import Control.Monad

import Debug.Trace
-- writeLine :: Line -> Text
-- writeLine (Line w t) = w <> t

---------------------------------------
-- Merging code blocks into a single one
-- data Block2 =
--   Comment2 [Line]
--   | HiddenCode2 [Line]
--   | Code2 [Line]


-- intoBlock2 :: [Block] -> [Block2]
-- intoBlock2 = f []
--   where makeCode :: [Line] -> [Block2]
--         makeCode [] = []
--         makeCode lines = [Code2 (Prelude.reverse lines)]

--         f :: [Line] -> [Block]-> [Block2]
--         f codelines [] = makeCode codelines
--         f codelines ((Code line) : xs) = f (line : codelines) xs
--         f codelines ((Comment com) : xs) = makeCode codelines ++ [Comment2 com] ++ f [] xs
--         f codelines ((HiddenCode com) : xs) = makeCode codelines ++ [HiddenCode2 com] ++ f [] xs

-------------------------------------------------------------------------
-- Parsing theorems and proofs
-------------------------------------------------------------------------


generateLiterate :: [SpecialCommand] -> Text -> MBRes Text
generateLiterate cmd s =
  let r = do res <- doParseLL s
             res2 <- doParseML cmd res
             return (tshow res2)

      r2 = case r of
              Left err -> Left $ "Low level parsing error: " <> err
              Right val -> Right val
  in r2

generateCommands :: [Text] -> MBRes [SpecialCommand]
generateCommands ts =
  let res = mapM doParseCommands ts
  in join <$> res



  -- "\\begin{code}\n"
  -- ++ s
  -- ++ "\\end{code}\n"

templatefileMainTex :: IO FilePath
templatefileMainTex = getDataFileName "templates/screport.tex.metabuild-template"

generateMainTex :: [FilePath] -> IO Text
generateMainTex files = do
  file <- templatefileMainTex
  template <- TIO.readFile file

  let content = replace "{{CONTENT}}" makeIncludes template

  return content
  where makeIncludes :: Text
        makeIncludes = T.concat ((\a -> T.pack ("\\input{" ++  a ++ "}\n")) <$> files)

templatefileAgdaSty :: IO FilePath
templatefileAgdaSty = getDataFileName "templates/agda.sty.metabuild-template"

generateAgdaSty :: IO Text
generateAgdaSty = do
  file <- templatefileAgdaSty
  content <- TIO.readFile file
  return content


  -- "\\begin{document}"
  -- ++ concat ((\a -> ("include" ++ a ++ "\n")) <$> files)
  -- ++ "\\end{document}"

