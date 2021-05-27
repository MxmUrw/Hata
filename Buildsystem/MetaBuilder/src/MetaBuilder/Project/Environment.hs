
module MetaBuilder.Project.Environment where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Shake
import MetaBuilder.Core


data ProjectEnv = ProjectEnv
  {
    projectRootFile :: FilePath
  }
  deriving (Show)

getEnvironment :: IO ProjectEnv
getEnvironment = do
  rootFile <- findProjectRootFile
  return (ProjectEnv rootFile)

------------------------------------------------------------
-- Finding the root file

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

