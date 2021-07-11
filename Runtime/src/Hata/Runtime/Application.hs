
module Hata.Runtime.Application where

import Hata.Runtime.Application.Render.Definition
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

data HataError =
  ParseError Text

data Event =
  Event_ReadFile Text
  | Event_KeyPress Text

data Reaction a =
  Reaction_NewWindow (a -> [Cmd])
  | Reaction_PrintDebug Text
  | Reaction_Exit

-- class Executable a where
--   init :: a
--   actOn :: Event -> a -> ([Reaction], a)

-- data ExecutableDict a = Executable a => ExecutableDict


data Executable a = Executable
  { initExec :: a
  , stepExec :: (Event -> a -> ([Reaction a], a))
  }

data RegisterExecutable where
  RegisterExecutable :: Text -> Executable a -> RegisterExecutable



