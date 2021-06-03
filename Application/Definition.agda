
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


