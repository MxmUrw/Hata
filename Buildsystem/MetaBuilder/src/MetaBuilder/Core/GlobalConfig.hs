
module MetaBuilder.Core.GlobalConfig where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core.Notation
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
  deriving (Show)

deriveExtraProjectConfig_Global :: FilePath -> GlobalConfig -> IO ExtraGlobalConfig
deriveExtraProjectConfig_Global rootfile gpc = do
  let root = takeDirectory rootfile
  let buildAbDir = root </> gpc.>buildRelDir
  let binAbDir   = root </> gpc.>binRelDir
  metabuilder_AbFile <- getExecutablePath
  home_AbDir <- getHomeDirectory
  return ExtraGlobalConfig
     { rootAbDir  = root
     , root_AbFile = rootfile
     , buildAbDir = buildAbDir
     , binAbDir   = binAbDir
     , metabuilder_AbFile = metabuilder_AbFile
     , home_AbDir = home_AbDir
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






