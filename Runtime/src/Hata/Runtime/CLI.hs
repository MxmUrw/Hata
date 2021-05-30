
module Hata.Runtime.CLI where

import Options.Applicative
import Data.Semigroup ((<>))

import Hata.Runtime.Application
import MAlonzo.Code.Application.Main
import qualified Data.Text as T
import Data.List

data HataArgs = HataArgs
  {
    appName :: String
  , targetFile :: String
  }

pArgs :: Parser HataArgs
pArgs = HataArgs
  <$> argument str (metavar "APP")
  <*> argument str (metavar "FILE")
  -- strOption (long "app"
  --               <> )

opts :: ParserInfo HataArgs
opts = info (pArgs <**> helper)
  ( fullDesc
  <> progDesc "Print a greeting for TARGET"
  <> header "hello - a test for optparse-applicative" )

execute :: IO ()
execute = do
  -- parse command line options
  (HataArgs appName targetFile) <- execParser opts

  let applist = getApplicationList
  let filtered_list = [func | (Execute name func) <- applist , name == T.pack appName]

  -- check if we have such an app
  case filtered_list of
    [func] -> do
      putStrLn "Reading file."
      file_content <- readFile targetFile
      putStrLn "Executing app."
      let result = func (T.pack file_content)
      putStrLn $ "Result is:" <> (T.unpack result)

    -- throw errors if we find to few/many apps
    [] -> putStrLn $ "Error: no app with the name '" <> appName <> "' exists."
    _ -> putStrLn $ "Error: multiple apps with the name '" <> appName <> "' exist."



