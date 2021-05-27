
module MetaBuilder.Project.Collection where

import MetaBuilder.Imports.Shake
import MetaBuilder.Project.Environment


data Collection = Collection
--   { globalConfig         :: GlobalConfig
--   , agdaProject          :: Maybe AgdaProjectConfig
--   , agdaPublishProject   :: Maybe AgdaPublishProjectConfig
--   , haskellStackProjects :: [HaskellStackProjectConfig]
--   } deriving (Generic)
-- instance FromJSON Collection

-- data ExtraCollection = ExtraCollection
--   { extraGlobalConfig         :: ExtraGlobalConfig
--   , extraAgdaProject          :: Maybe ExtraAgdaProjectConfig
--   , extraAgdaPublishProject   :: Maybe ExtraAgdaPublishProjectConfig
--   , extraHaskellStackProjects :: [ExtraHaskellStackProjectConfig]
--   }

getCollection :: ProjectEnv -> IO Collection
getCollection = undefined

makeRules :: Collection -> Rules ()
makeRules = undefined

