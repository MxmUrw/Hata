
module Verification.Core.Set.Set.Definition where

open import Verification.Core.Conventions renaming (isSet to isSetᵈ)

record isSet (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field fillPath-Set : isSetᵈ A

Set : ∀ 𝑖 -> 𝒰 _
Set 𝑖 = 𝒰 𝑖 :& isSet

macro
  𝐒𝐞𝐭 : ∀ 𝑖 -> SomeStructure
  𝐒𝐞𝐭 𝑖 = #structureOn (Set 𝑖)






