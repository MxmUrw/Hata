
module MetaBuilder.Core.ProjectType where

import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core.GlobalConfig

-- import qualified Data.Text as T
-- import qualified Data.Text.IO as TIO



class (Generic d, FromJSON d) => ProjectType d e | e -> d where
  deriveExtraConfig :: ExtraGlobalConfig -> d -> e
  makeRules :: ExtraGlobalConfig -> e -> Rules ()



