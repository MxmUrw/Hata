
module Verification.Experimental.Set.Set.Definition where

open import Verification.Experimental.Conventions


Set : ∀ 𝑖 -> 𝒰 _
Set 𝑖 = 𝒰 𝑖 :& isSet

macro
  𝐒𝐞𝐭 : ∀ 𝑖 -> SomeStructure
  𝐒𝐞𝐭 𝑖 = #structureOn (Set 𝑖)






