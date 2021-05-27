
module MetaBuilder.Project.Collection where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core
import MetaBuilder.Project.Environment
import MetaBuilder.Project.Type.Haskell

import qualified Data.Yaml

data Collection = Collection
  { globalConfig         :: GlobalConfig
  -- , agdaProject          :: Maybe AgdaProjectConfig
  -- , agdaPublishProject   :: Maybe AgdaPublishProjectConfig
  , haskellStackProjects :: [HaskellStackProjectConfig]
  } deriving (Generic)
instance FromJSON Collection

data ExtraCollection = ExtraCollection
  { extraGlobalConfig         :: ExtraGlobalConfig
  -- , extraAgdaProject          :: Maybe ExtraAgdaProjectConfig
  -- , extraAgdaPublishProject   :: Maybe ExtraAgdaPublishProjectConfig
  , extraHaskellStackProjects :: [ExtraHaskellStackProjectConfig]
  }
  deriving (Show)

getCollection :: ProjectEnv -> IO ExtraCollection
getCollection env = do
  col <- Data.Yaml.decodeFileThrow (env.>projectRootFile)
  deriveExtraCollection env col

-- readCollection :: IO Collection
-- readCollection = do
--   rootFile <- findProjectRootFile
--   Data.Yaml.decodeFileThrow rootFile

makeCollectionRules :: ExtraCollection -> Rules ()
makeCollectionRules col = do
  mapM (makeRules (col.>extraGlobalConfig)) (col.>extraHaskellStackProjects)
  makeCleanRules (col.>extraGlobalConfig)
  return ()

makeCleanRules :: ExtraGlobalConfig -> Rules ()
makeCleanRules epc = do
  phony "clean" $ do
    putInfo $ "Cleaning files in " ++ epc.>buildAbDir
    removeFilesAfter (epc.>buildAbDir) ["//*"]
    putInfo $ "Cleaning files in " ++ epc.>binAbDir
    removeFilesAfter (epc.>binAbDir) ["//*"]


deriveExtraCollection :: ProjectEnv -> Collection -> IO ExtraCollection
deriveExtraCollection env c = do
  extraGlobalConfig <- deriveExtraProjectConfig_Global (env.>projectRootFile) (c.>globalConfig)
  -- let extraAgdaProject  = deriveExtraProjectConfig_Agda extraGlobalConfig <$> (c.>agdaProject)
  -- let extraAgdaPublishProject  = deriveExtraProjectConfig_AgdaPublish extraGlobalConfig <$> (c.>agdaPublishProject)
  let extraHaskellStackProjects = deriveExtraConfig extraGlobalConfig <$> (c.>haskellStackProjects)
  return ExtraCollection
     { extraGlobalConfig         = extraGlobalConfig
     -- , extraAgdaProject          = extraAgdaProject
     -- , extraAgdaPublishProject   = extraAgdaPublishProject
     , extraHaskellStackProjects = extraHaskellStackProjects
     }

