module Hata.Runtime.Main
    ( run
    ) where

import Hata.Runtime.Application
import Hata.Runtime.CLI
-- import MAlonzo.Code.Application.Main
-- import qualified Data.Text as T
-- import Data.List

run :: IO ()
run = execute
  -- let applist = getApplicationList
  -- let names = (\(Execute name _) -> name) <$> applist
  -- putStrLn (intercalate ", " (T.unpack <$> names))




