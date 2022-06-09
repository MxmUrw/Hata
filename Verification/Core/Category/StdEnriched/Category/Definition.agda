
module Verification.Core.Category.StdEnriched.Category.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition

module _ (𝑗 : 𝔏) {𝑖 : 𝔏 ^ 3} (𝒞 : Category 𝑖) where

-- record EnCategoryType (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
--   constructor [_,_,_]
--   field Cell₀ᵈ : 𝒰 (𝑖 ⌄ 0)
--   field Cell₁ᵈ : Cell₀ᵈ -> Cell₀ᵈ -> 𝒰 (𝑖 ⌄ 1)
--   field Cell₂ᵈ : ∀{a b : Cell₀ᵈ} -> (f g : Cell₁ᵈ a b) -> 𝒰 (𝑖 ⌄ 2)


