

module Verification.Core.Data.Type.Definition where

open import Verification.Conventions
open import Verification.Core.Data.Lift.Definition

macro
  𝐓𝐲𝐩𝐞' : ∀ (𝑖 : 𝔏) -> SomeStructure
  𝐓𝐲𝐩𝐞' (𝑖) = #structureOn (Lift-Cat {𝑖 , 𝑖 ⁺ , 𝑖 ⁺} (𝒰' (𝑖 ⌄ 0)))




