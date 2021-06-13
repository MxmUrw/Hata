

module Verification.Experimental.Category.Multi.Definition where

open import Verification.Conventions
open import Verification.Experimental.Category.Std.Category.Definition

record isMultiCategory (𝒞 : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field Hom-MC : ∀ n -> (Fin n -> 𝒞) -> 𝒞 -> 𝒰 𝑗
        id-MC : ∀{a : 𝒞} -> Hom-MC 1 (const a) a
        -- comp-MC : ∀(as : List (List 𝒞 ×-𝒰 𝒞)) -> ()




