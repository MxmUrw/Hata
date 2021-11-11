
module Verification.Core.Category.Std.Groupoid.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

record isGroupoid (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field {{isIso:hom}} : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{ϕ : a ⟶ b} -> isIso (hom ϕ)





