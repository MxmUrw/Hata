
module Verification.Application.Definition where

open import Verification.Experimental.Conventions
open import Verification.Application.Render.Definition
open import Verification.Experimental.Data.Product.Definition

{-# FOREIGN GHC import Hata.Runtime.Application #-}

data Printable : 𝒰₀ where
  PInt : Int -> Printable
  PFrac : Int -> Int -> Printable
  PString : String -> Printable
  PAnnot : Printable -> Printable -> Printable
  PList : List Printable -> Printable


{-# COMPILE GHC Printable = data Printable (PInt | PFrac | PString | PAnnot | PList) #-}


data Application : 𝒰₀ where
  execute : String -> (String -> Printable) -> Application

{-# COMPILE GHC Application = data Application (Execute) #-}

data Error : 𝒰₀ where
  parseError : String -> Error

{-# COMPILE GHC Error = data HataError (ParseError) #-}



--------------------------------------------------------------------
-- Executable interface




data Event : 𝒰₀ where
  Event-ReadFile : String -> Event
  Event-KeyPress : String -> Event
  -- Event-CairoDraw : Event

{-# COMPILE GHC Event = data Event (Event_ReadFile | Event_KeyPress) #-}

data Reaction (A : 𝒰₀) : 𝒰₀ where
  Reaction-NewWindow : (A -> List Cairo.Cmd) -> Reaction A
  -- Reaction-CairoDraw : Cairo.Cmd -> Reaction A
  Reaction-PrintDebug : String -> Reaction A
  Reaction-Exit : Reaction A

{-# COMPILE GHC Reaction = data Reaction (Reaction_NewWindow | Reaction_PrintDebug | Reaction_Exit) #-}


record Executable (A : 𝒰₀) : 𝒰₀ where
  constructor executable
  field init : A
  field step : Event -> A -> (List (Reaction A) ×~ A)


{-# COMPILE GHC Executable = data Executable (Executable) #-}

data RegisterExecutable : 𝒰₁ where
  registerExecutable : ∀{A} -> String -> Executable A -> RegisterExecutable

{-# COMPILE GHC RegisterExecutable = data RegisterExecutable (RegisterExecutable) #-}



