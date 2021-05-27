
module MetaBuilder.Project.Type.Haskell where

import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core


data HaskellStackProjectConfig = HaskellStackProjectConfig
  { haskellStackBin_RelFile   :: FilePath
  , haskellStackSource_RelDir :: FilePath
  , haskellStackAutobuild     :: Bool
  , installGlobal             :: Bool
  }
  deriving (Generic)
instance FromJSON HaskellStackProjectConfig


data ExtraHaskellStackProjectConfig = ExtraHaskellStackProjectConfig
  { haskellStackBin_AbFile     :: FilePath
  , haskellStackSource_AbDir   :: FilePath
  -- original settings
  , originalHaskellStackConfig :: HaskellStackProjectConfig
  }

deriveExtraProjectConfig_HaskellStack :: ExtraGlobalConfig -> HaskellStackProjectConfig -> ExtraHaskellStackProjectConfig
deriveExtraProjectConfig_HaskellStack egpc hpc =
  let haskellStackBin_AbFile   = if hpc.>installGlobal
                                    then (egpc.>home_AbDir) </> ".local" </> "bin"  </> hpc.>haskellStackBin_RelFile <.> exe
                                    else egpc.>binAbDir </> hpc.>haskellStackBin_RelFile <.> exe
      haskellStackSource_AbDir = egpc.>rootAbDir </> hpc.>haskellStackSource_RelDir
  in ExtraHaskellStackProjectConfig
     { haskellStackBin_AbFile     = haskellStackBin_AbFile
     , haskellStackSource_AbDir    = haskellStackSource_AbDir
     , originalHaskellStackConfig  = hpc
     }

instance ProjectType HaskellStackProjectConfig ExtraHaskellStackProjectConfig where
  deriveExtraConfig = deriveExtraProjectConfig_HaskellStack
  makeRules = undefined


