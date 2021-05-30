
module Application.Definition where

open import Verification.Experimental.Conventions

{-# FOREIGN GHC import Hata.Runtime.Application #-}


data Application : 𝒰₀ where
  execute : String -> (String -> String) -> Application

{-# COMPILE GHC Application = data Application (Execute) #-}


