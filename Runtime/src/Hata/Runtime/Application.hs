
module Hata.Runtime.Application where

import Data.Text as T

data Application = Execute Text (Text -> Printable)

data Printable =
  PInt Integer
  | PFrac Integer Integer
  | PString Text
  | PAnnot Printable Printable
  | PList [Printable]

instance Show Printable where
  show (PInt n) = show n
  show (PFrac p q) = show (fromIntegral p / fromIntegral q) <> " (" <> show p <> "/" <> show q <> ")"
  show (PString t) = T.unpack t
  show (PAnnot p q) = show p <> show q
  show (PList ps) = show ps


