
module MetaBuilder.Core.GlobalConfig where

import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import System.Directory
import System.FilePath.Find as FP
import System.Environment.Executable

import GHC.Generics

import Control.Exception
import Control.Monad


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


data MBException
  = CouldNotFindRootFile
  | FoundMultipleRootFiles
  deriving (Typeable)

instance Show MBException where
  show CouldNotFindRootFile   = "Error: Could not find a .metabuild-root file."
  show FoundMultipleRootFiles = "Error: Found multiple .metabuild-root files in same directory."

instance Exception MBException

filterRoot :: FilePath -> Bool
filterRoot file = takeExtension file == ".metabuild-root"

findProjectRootFile_impl :: FilePath -> IO FilePath
findProjectRootFile_impl cur_dir = do
  files <- listDirectory cur_dir
  let filtered = filter filterRoot files
  case filtered of
    [] -> let parent = takeDirectory cur_dir
          in if (isDrive cur_dir || parent == cur_dir)
             then (throw CouldNotFindRootFile)
             else (findProjectRootFile_impl parent)
    [x] -> (return (cur_dir </> x))
    x:xs -> throw (FoundMultipleRootFiles)

findProjectRootFile :: IO FilePath
findProjectRootFile = do
  getCurrentDirectory >>= findProjectRootFile_impl





