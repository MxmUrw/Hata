
module Hata.Runtime.CLI where

import Options.Applicative
import Data.Semigroup ((<>))

import MAlonzo.Code.Application.Main
import qualified Data.Text as T
import Data.List

import Hata.Runtime.Application
import Hata.Runtime.EventLoop

data HataArgs = HataArgs
  {
    appName :: String
  , targetFile :: String
  }

pArgs :: Parser HataArgs
pArgs = HataArgs
  <$> argument str (metavar "APP")
  <*> strOption
    ( long "file"
    <> short 'f'
    <> metavar "FILE"
    <> value ""
    )
  -- auto (metavar "FILE" <> value Nothing)
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
  let filtered_list = [RegisterExecutable name func | (RegisterExecutable name func) <- applist , name == T.pack appName]

  let targetFile' = case targetFile of
        "" -> Nothing
        a -> Just a

  input <- mapM (\a -> putStrLn "Reading file." >> readFile a) targetFile'
  let events = case input of
        Nothing -> []
        (Just a) -> [Event_ReadFile (T.pack a)]

  -- check if we have such an app
  case filtered_list of
    [func] -> do
      putStrLn "Executing app."
      el_singleRun func events

    -- throw errors if we find to few/many apps
    [] -> putStrLn $ "Error: no app with the name '" <> appName <> "' exists."
    _ -> putStrLn $ "Error: multiple apps with the name '" <> appName <> "' exist."



