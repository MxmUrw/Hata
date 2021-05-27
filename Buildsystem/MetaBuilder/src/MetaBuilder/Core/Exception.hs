
module MetaBuilder.Core.Exception where

import MetaBuilder.Imports.Common
import MetaBuilder.Imports.Yaml

data MBException
  = CouldNotFindRootFile
  | FoundMultipleRootFiles
  deriving (Typeable)

instance Show MBException where
  show CouldNotFindRootFile   = "Error: Could not find a .metabuild-root file."
  show FoundMultipleRootFiles = "Error: Found multiple .metabuild-root files in same directory."

instance Exception MBException
