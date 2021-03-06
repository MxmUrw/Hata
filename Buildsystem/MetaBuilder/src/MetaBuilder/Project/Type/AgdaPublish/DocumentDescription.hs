
module MetaBuilder.Project.Type.AgdaPublish.DocumentDescription where

import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core

import qualified Data.Yaml as Yaml

data DocumentType = SCReport | Book
  deriving (Generic,Show)

instance FromJSON DocumentType

data DocumentDescription = DocumentDescription
  {
    documentTitle :: String
  , documentSubtitle :: Maybe String
  , documentAuthor :: String
  , documentDate :: String
  , documentType :: DocumentType
  , documentFilesAndHeadings :: [String]
  , notImportantFiles :: [FilePath]
  }
  deriving (Generic,Show)

instance FromJSON DocumentDescription

getDocumentRelFiles :: DocumentDescription -> [FilePath]
getDocumentRelFiles doc = filter f (doc.>documentFilesAndHeadings)
  where f ('=' : xs) = False
        f _ = True


generateDocumentBody :: DocumentDescription -> String -> [String] -> String
generateDocumentBody docdec docroot filesAndHeadings = concat $ f <$> filesAndHeadings
  where f ('=' : xs) = makeHeading' (documentType docdec) xs
        f xs         = makeInclude xs

        makeHeading' SCReport xs = makeHeading 1 xs
        makeHeading' Book xs     = makeHeading 0 xs

        makeHeading n ('=' : xs) = makeHeading (n + 1) xs
        makeHeading 0 xs = "\\part{" <> xs <> "}\n"
        makeHeading 1 xs = "\\chapter{" <> xs <> "}\n"
        makeHeading 2 xs = "\\section{" <> xs <> "}\n"
        makeHeading 3 xs = "\\subsection{" <> xs <> "}\n"
        makeHeading _ xs = "\\subsubsection{" <> xs <> "}\n"

        makeInclude xs = "\\input{" <> toStandard (docroot </> dropExtensions xs) <> "}\n"

