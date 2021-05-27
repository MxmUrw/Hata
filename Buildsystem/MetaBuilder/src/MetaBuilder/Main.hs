module MetaBuilder.Main
    ( run
    ) where

import MetaBuilder.Project.Environment
import MetaBuilder.Project.Collection

someFunc :: IO ()
someFunc = putStrLn "someFunc"

run :: IO ()
run = do
  env <- getEnvironment
  putStrLn $ show env
  -- collection <- getCollection env
  -- putStrLn $ show collection
  return ()

