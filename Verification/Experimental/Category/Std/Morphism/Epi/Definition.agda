
module Verification.Experimental.Category.Std.Morphism.Epi.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Morphism
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Definition
-- open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
-- open import Verification.Experimental.Category.Std.Functor.Faithful
-- open import Verification.Experimental.Category.Std.Functor.Full
-- open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily
-- open import Verification.Experimental.Category.Std.Functor.Image
-- open import Verification.Experimental.Category.Std.Category.Notation.Associativity



module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record isEpi {a b : 𝒞} (ϕ : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor epi
    field cancel-epi : ∀{x : 𝒞} -> ∀{α β : b ⟶ x} -> ϕ ◆ α ∼ ϕ ◆ β -> α ∼ β

  open isEpi {{...}} public

  isEpi:id : ∀{a : 𝒞} -> isEpi (id {a = a})
  isEpi:id = epi (λ p → unit-l-◆ ⁻¹ ∙ p ∙ unit-l-◆)


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  --------------------------------------------------------------
  -- reflection

  record isEpiReflecting (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field reflect-isEpi : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{ϕ : a ⟶ b} -> isEpi (map {{of F}} ϕ) -> isEpi ϕ

  open isEpiReflecting {{...}} public

  --------------------------------------------------------------
  -- preservation
  record isEpiPreserving (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field preserve-isEpi : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{ϕ : a ⟶ b} -> isEpi ϕ -> isEpi (map {{of F}} ϕ)

  open isEpiPreserving {{...}} public
