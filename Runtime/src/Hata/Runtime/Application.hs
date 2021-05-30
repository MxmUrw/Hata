
module Hata.Runtime.Application where

import Data.Text as T

data Application = Execute Text (Text -> Text)


