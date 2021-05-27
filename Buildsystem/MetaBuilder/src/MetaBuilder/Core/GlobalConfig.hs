
module MetaBuilder.Core.GlobalConfig where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Yaml
-- import MetaBuilder.Project.Environment


data GlobalConfig = GlobalConfig
  { buildRelDir      :: FilePath
  , binRelDir        :: FilePath
  }
  deriving (Generic)
instance FromJSON GlobalConfig

data ExtraGlobalConfig = ExtraGlobalConfig
  { rootAbDir            :: FilePath
  , root_AbFile          :: FilePath
  , buildAbDir           :: FilePath
  , binAbDir             :: FilePath
  , metabuilder_AbFile    :: FilePath
  , home_AbDir           :: FilePath
  }


-- module MetaBuilder.Core.GlobalConfig where

-- import MetaBuilder.Imports.Yaml
-- import MetaBuilder.Imports.Shake

-- import qualified Data.Text as T
-- import qualified Data.Text.IO as TIO

-- import System.Directory
-- import System.FilePath.Find as FP
-- import System.Environment.Executable

-- import GHC.Generics

-- import Control.Exception
-- import Control.Monad


-- data GlobalConfig = GlobalConfig
--   { buildRelDir      :: FilePath
--   , binRelDir        :: FilePath
--   }
--   deriving (Generic)
-- instance FromJSON GlobalConfig

-- data ExtraGlobalConfig = ExtraGlobalConfig
--   { rootAbDir            :: FilePath
--   , root_AbFile          :: FilePath
--   , buildAbDir           :: FilePath
--   , binAbDir             :: FilePath
--   , metabuilder_AbFile    :: FilePath
--   , home_AbDir           :: FilePath
--   }


-- data MBException
--   = CouldNotFindRootFile
--   | FoundMultipleRootFiles
--   deriving (Typeable)

-- instance Show MBException where
--   show CouldNotFindRootFile   = "Error: Could not find a .metabuild-root file."
--   show FoundMultipleRootFiles = "Error: Found multiple .metabuild-root files in same directory."

-- instance Exception MBException






