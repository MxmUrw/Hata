
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module MetaBuilder.Project.Type.AgdaPublish.Persistent where

import Data.Typeable
import Data.Aeson
import qualified Data.Yaml
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import GHC.Generics
import Development.Shake.Classes

data IsSubscript = IsSubscript | NotSubscript
  deriving (Show, Eq, Generic)
instance FromJSON IsSubscript
instance ToJSON IsSubscript
instance Hashable IsSubscript
instance Binary IsSubscript
instance NFData IsSubscript

data FontStyle = MathRM | MathBF | Sans
  deriving (Show, Eq, Generic)
instance FromJSON FontStyle
instance ToJSON FontStyle
instance Hashable FontStyle
instance Binary FontStyle
instance NFData FontStyle

data Format = Format FontStyle IsSubscript
  deriving (Show, Eq, Generic)
instance FromJSON Format
instance ToJSON Format
instance Hashable Format
instance Binary Format
instance NFData Format

data SpecialCommand =
  NotationSC FontStyle String String -- fmt replacement toBeReplaced
  | NotationSA String
  | NotationSC_Short FontStyle String String
  | NotationRewrite String String
  deriving (Show, Eq, Generic)
instance FromJSON SpecialCommand
instance ToJSON SpecialCommand
instance Hashable SpecialCommand
instance Binary SpecialCommand
instance NFData SpecialCommand
