
module MetaBuilder.Project.Collection where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core
import MetaBuilder.Project.Environment
import MetaBuilder.Project.Type.Haskell
import MetaBuilder.Project.Type.Agda
import MetaBuilder.Project.Type.AgdaPublish

import qualified Data.Yaml

data Collection = Collection
  { globalConfig         :: GlobalConfig
  , agdaProjects          :: [AgdaProjectConfig]
  , agdaPublishProjects  :: [AgdaPublishProjectConfig]
  , haskellStackProjects :: [HaskellStackProjectConfig]
  } deriving (Generic)
instance FromJSON Collection

data ExtraCollection = ExtraCollection
  { extraGlobalConfig         :: ExtraGlobalConfig
  , extraAgdaProjects          :: [ExtraAgdaProjectConfig]
  , extraAgdaPublishProjects   :: [ExtraAgdaPublishProjectConfig]
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
  mapM (makeRules (col.>extraGlobalConfig)) (col.>extraAgdaProjects)
  mapM (makeRules (col.>extraGlobalConfig)) (col.>extraAgdaPublishProjects)
  makeCleanRules (col.>extraGlobalConfig)
  return ()

makeCleanRules :: ExtraGlobalConfig -> Rules ()
makeCleanRules epc = do
  phony "clean" $ do
    putInfo $ "Cleaning files in " ++ epc.>buildAbDir
    removeFilesAfter (epc.>buildAbDir) ["" <//> "*"]
    putInfo $ "Cleaning files in " ++ epc.>binAbDir
    removeFilesAfter (epc.>binAbDir) ["" <//> "*"]


deriveExtraCollection :: ProjectEnv -> Collection -> IO ExtraCollection
deriveExtraCollection env c = do
  extraGlobalConfig <- deriveExtraProjectConfig_Global (env.>projectRootFile) (c.>globalConfig)
  let extraAgdaProjects  = deriveExtraProjectConfig_Agda extraGlobalConfig <$> (c.>agdaProjects)
  let extraAgdaPublishProjects  = deriveExtraProjectConfig_AgdaPublish extraGlobalConfig <$> (c.>agdaPublishProjects)
  let extraHaskellStackProjects = deriveExtraConfig extraGlobalConfig <$> (c.>haskellStackProjects)
  return ExtraCollection
     { extraGlobalConfig         = extraGlobalConfig
     , extraAgdaProjects          = extraAgdaProjects
     , extraAgdaPublishProjects   = extraAgdaPublishProjects
     , extraHaskellStackProjects = extraHaskellStackProjects
     }

