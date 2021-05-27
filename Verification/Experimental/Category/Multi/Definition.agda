

module Verification.Experimental.Category.Multi.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition

record isPlainMultiCat (𝒞 : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Hom-MC : List 𝒞 -> 𝒞 -> 𝒰 𝑗
        id-MC : ∀{a : 𝒞} -> Hom-MC (a ∷ []) a
        -- comp-MC : ∀(as : List (List 𝒞 ×-𝒰 𝒞)) -> ()




