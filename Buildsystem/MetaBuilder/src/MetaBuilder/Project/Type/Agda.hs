
module MetaBuilder.Project.Type.Agda where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Yaml
import MetaBuilder.Imports.Shake
import MetaBuilder.Core



data AgdaProjectConfig = AgdaProjectConfig
  -- all paths should be relative
  { sourceRelDir               :: FilePath
  , sourceOverwrite_RelDir     :: FilePath
  , mainRelFile                :: FilePath
  , agdaBin_RelFile            :: String
  , haskellStackTemplateRelDir :: FilePath
  , agdaAutobuild              :: Bool
  , libraryDefinitions_Filename :: String
  }
  deriving (Generic, Show)
instance FromJSON AgdaProjectConfig

data ExtraAgdaProjectConfig = ExtraAgdaProjectConfig
  -- absolute versions of paths in `AgdaProjectConfig`
  { originalSource_AbDir                :: FilePath
  , originalSourceOverwrite_AbDir       :: FilePath
  , transpilationSource_AbDir           :: FilePath
  -- , transpilationSourceOverwrite_AbDir  :: FilePath
  , transpilationTarget_AbDir           :: FilePath
  , agdaTarget_AbDir                    :: FilePath
  , agdaBin_AbFile                      :: FilePath
  , mainTranspilationSource_AbFile      :: FilePath
  -- derived paths
  , haskellStack_TemplateSource_AbDir   :: FilePath
  , haskellStack_TemplateTarget_AbDir   :: FilePath
  -- fixed paths
  , ghcshim_AbFile                      :: FilePath
  -- original settings
  , originalAgdaConfig                  :: AgdaProjectConfig
  , libraryDefinitions_Source_AbFile  :: FilePath
  , libraryDefinitions_Target_AbFile  :: FilePath
  }
  deriving (Show)


deriveExtraProjectConfig_Agda :: ExtraGlobalConfig -> AgdaProjectConfig -> ExtraAgdaProjectConfig
deriveExtraProjectConfig_Agda egpc ap =
  let transpilationSource_AbDir = egpc.>buildAbDir </> "agdabuild" </> ap.>sourceRelDir
  in
  ExtraAgdaProjectConfig
  {
  -- original sources
  originalSource_AbDir                = egpc.>rootAbDir </> ap.>sourceRelDir
  , originalSourceOverwrite_AbDir     = egpc.>rootAbDir </> ap.>sourceOverwrite_RelDir
  -- transpilation sources:
  , transpilationSource_AbDir         = transpilationSource_AbDir
  , mainTranspilationSource_AbFile    = transpilationSource_AbDir </> ap.>mainRelFile
  , haskellStack_TemplateSource_AbDir = egpc.>rootAbDir </> ap.>haskellStackTemplateRelDir
  -- targets:
  , agdaTarget_AbDir                  = egpc.>buildAbDir </> ap.>haskellStackTemplateRelDir </> "src"
  , transpilationTarget_AbDir         = egpc.>buildAbDir </> ap.>haskellStackTemplateRelDir </> "src" </> "MAlonzo" </> "Code"
  , haskellStack_TemplateTarget_AbDir = egpc.>buildAbDir </> ap.>haskellStackTemplateRelDir
  , agdaBin_AbFile                    = egpc.>binAbDir </> ap.>agdaBin_RelFile <.> exe
  -- fixed paths:
  , ghcshim_AbFile                    = egpc.>buildAbDir </> "ghcshim" </> "ghc"
  , libraryDefinitions_Source_AbFile = egpc.>rootAbDir </> ap.>libraryDefinitions_Filename
  , libraryDefinitions_Target_AbFile = transpilationSource_AbDir </> ap.>libraryDefinitions_Filename
  , originalAgdaConfig                = ap
  }


makeRules_AgdaProject :: ExtraGlobalConfig -> ExtraAgdaProjectConfig -> Rules ()
makeRules_AgdaProject egpc eapc = do
  if (eapc.>originalAgdaConfig.>agdaAutobuild)
    then want [eapc.>agdaBin_AbFile]
    else return ()

  -- TODO: WARNING!
  -- we test here for whether the directory path contains "_build", but it is in no way guaranteed that
  -- the build path will always contain this string!
  let getGoodDirectoryFilesIO path patterns = do
        files <- liftIO $ getDirectoryFilesIO path patterns
        let good_files = filter (\f -> let dirs = splitDirectories f in not (or [elem "_build" dirs, elem ".stack-work" dirs])) files
        return good_files

  phony (eapc.>originalAgdaConfig.>agdaBin_RelFile) $ do
    need [eapc.>agdaBin_AbFile]

  haskellStack_Template_Files <- liftIO $ getDirectoryFilesIO (eapc.>haskellStack_TemplateSource_AbDir) ["//*.hs", "//*.yaml"]
  let filtered_haskellStack_Template_Files = filter (\f -> not (elem ".stack-work" (splitDirectories f))) haskellStack_Template_Files
  let haskellStack_TemplateSource_Files = ((eapc.>haskellStack_TemplateSource_AbDir </>) <$> filtered_haskellStack_Template_Files)
  let haskellStack_TemplateTarget_Files = ((eapc.>haskellStack_TemplateTarget_AbDir </>) <$> filtered_haskellStack_Template_Files)


  ----------------------------------------------
  -- Copying the .agda-lib file
  (eapc.>libraryDefinitions_Target_AbFile) %> \file -> do
    copyFile' (eapc.>libraryDefinitions_Source_AbFile) (eapc.>libraryDefinitions_Target_AbFile)

  ----------------------------------------------
  -- Original Files ---> Transpilation source files

  -- copy the original files to their transpilation source directory
  (eapc.>transpilationSource_AbDir ++ "//*") %> \file -> do
    -- given a target file, we find it's relative path
    let relfile = makeRelative (normalise (eapc.>transpilationSource_AbDir)) (normalise file)

    let sourceFile1 = eapc.>originalSource_AbDir </> relfile
    let sourceFile2 = eapc.>originalSourceOverwrite_AbDir </> relfile
    let targetFile = eapc.>transpilationSource_AbDir </> relfile

    -- check if sourceFile2 exists (i.e., file should be overwritten)
    file2Exists <- doesFileExist sourceFile2
    let sourceFile = case file2Exists of
          True  -> sourceFile2
          False -> sourceFile1

    -- putInfo $ "------------------ copying -------------------"
    -- putInfo $ " relative to " <> (eapc.>transpilationSource_AbDir)
    -- putInfo $ "- relfile:        " <> relfile
    -- putInfo $ "- file:        " <> file
    -- putInfo $ "- sourceFile1: " <> sourceFile1
    -- putInfo $ "- sourceFile2: " <> sourceFile2
    -- putInfo $ "- targetFile:  " <> targetFile

    -- putInfo $ "I want to copy file " <> sourceFile <> " to " <> targetFile
    liftIO $ createDirectoryIfMissing True (takeDirectory targetFile)

    copyFile' sourceFile targetFile

  ----------------------------------------------
  -- Transpilation source files (.agda) ---> Transpilation target (.hs)

  transpilation_Files <- liftIO $ getGoodDirectoryFilesIO (normalise (eapc.>originalSource_AbDir)) ["//*.agda"]
  let transpilationSource_Files = ((\f -> eapc.>transpilationSource_AbDir </> f)            <$> transpilation_Files)
  let transpilationTarget_Files = ((\f -> eapc.>transpilationTarget_AbDir </> f -<.> ".hs") <$> transpilation_Files)

  transpilationTarget_Files &%> \files -> do
    need $ transpilationSource_Files
      ++ [ eapc.>ghcshim_AbFile
         , eapc.>libraryDefinitions_Target_AbFile]

    let ghc_shimpath = takeDirectory (eapc.>ghcshim_AbFile)
    cmd_ "agda" [AddPath [ghc_shimpath] [], Cwd (eapc.>transpilationSource_AbDir)] ["--compile", "--compile-dir=" ++ eapc.>agdaTarget_AbDir, eapc.>mainTranspilationSource_AbFile]

  ----------------------------------------------
  -- last step (... -- stack --> binaries)
  eapc.>agdaBin_AbFile %> \a -> do
    need (transpilationTarget_Files ++ haskellStack_TemplateTarget_Files)
    cmd_ "stack" (Cwd (eapc.>haskellStack_TemplateTarget_AbDir)) ["install", "--local-bin-path=" ++ egpc.>binAbDir]


  (eapc.>haskellStack_TemplateTarget_AbDir ++ "//*") %> \file -> do
    let relfile = makeRelative (eapc.>haskellStack_TemplateTarget_AbDir) file
    let sourceFile = eapc.>haskellStack_TemplateSource_AbDir </> relfile
    let targetFile = eapc.>haskellStack_TemplateTarget_AbDir </> relfile
    putInfo $ "Copying " ++ relfile ++ " from " ++ eapc.>haskellStack_TemplateSource_AbDir
    copyFile' sourceFile targetFile

  (eapc.>ghcshim_AbFile) %> \file -> do
    putInfo "Generating ghc shim"
    liftIO $ writeFile file "#!/bin/bash\n echo \"==== executing shim ====\""
    perm <- liftIO $ getPermissions file
    let perm2 = setOwnerExecutable True perm
    liftIO $ setPermissions file perm2


instance ProjectType AgdaProjectConfig ExtraAgdaProjectConfig where
  deriveExtraConfig = deriveExtraProjectConfig_Agda
  makeRules = makeRules_AgdaProject

