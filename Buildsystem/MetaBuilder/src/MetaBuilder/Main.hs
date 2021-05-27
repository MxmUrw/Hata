module MetaBuilder.Main
    ( run
    ) where

import MetaBuilder.Imports.Shake
import MetaBuilder.Core
import MetaBuilder.Project.Environment
import MetaBuilder.Project.Collection

run :: IO ()
run = do
  -- read in the current environment
  -- (currently only the path to the root file)
  env <- getEnvironment

  -- read the root file into a "collection" of projects
  col <- getCollection env

  -- set the directory for shake's generated files
  -- and number of threads
  let options = shakeOptions{shakeFiles=col.>extraGlobalConfig.>buildAbDir, shakeThreads=1}

  -- execute shake with rules made from the collection
  shakeArgs options (makeCollectionRules col)


