
module Application.Definition where

open import Verification.Experimental.Conventions

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

record _×-H_ (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _,_
  field fst : A
  field snd : B


{-# FOREIGN GHC type AgdaProduct a b = (,) #-}
-- {-# FOREIGN GHC makeProduct a b = (a,b) #-}
{-# COMPILE GHC _×-H_ = data AgdaProduct ((,)) #-}



data Event : 𝒰₀ where
  Event-ReadFile : String -> Event

{-# COMPILE GHC Event = data Event (Event_ReadFile) #-}

data Reaction : 𝒰₀ where
  Reaction-NewWindow : Reaction
  Reaction-PrintDebug : String -> Reaction
  Reaction-Exit : Reaction

{-# COMPILE GHC Reaction = data Reaction (Reaction_NewWindow | Reaction_PrintDebug | Reaction_Exit) #-}


record Executable (A : 𝒰₀) : 𝒰₀ where
  constructor executable
  field init : A
  field step : Event -> A -> (List Reaction ×-H A)


{-# COMPILE GHC Executable = data Executable (Executable) #-}

data RegisterExecutable : 𝒰₁ where
  registerExecutable : ∀{A} -> String -> Executable A -> RegisterExecutable

{-# COMPILE GHC RegisterExecutable = data RegisterExecutable (RegisterExecutable) #-}



