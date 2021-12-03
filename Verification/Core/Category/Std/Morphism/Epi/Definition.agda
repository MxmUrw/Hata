
module Verification.Core.Category.Std.Morphism.Epi.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition



-- | Let [..] [] be a category.
module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where

  -- [Definition]
  -- | An arrow |f : a ⟶ b| in |𝒞| is called an /epimorphism/ if
  -- the following condition holds:
  record isEpi {a b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor epi
    -- | For any two other arrows we can do ., ie.:
    field cancel-epi : ∀{x : 𝒞} -> ∀{α β : b ⟶ x} -> f ◆ α ∼ f ◆ β -> α ∼ β


  open isEpi {{...}} public

  -- //

  -- [Hide]
  isEpi:id : ∀{a : 𝒞} -> isEpi (id {a = a})
  isEpi:id = epi (λ p → unit-l-◆ ⁻¹ ∙ p ∙ unit-l-◆)

  isEpi:◆ : ∀{a b c : 𝒞} -> {f : a ⟶ b} -> {g : b ⟶ c} -> isEpi f -> isEpi g -> isEpi (f ◆ g)
  isEpi:◆ p q = epi (λ gfα∼gfβ → cancel-epi (cancel-epi (assoc-r-◆ ∙ gfα∼gfβ ∙ assoc-l-◆)) )
    where
      instance
        _ = p
        _ = q


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  --------------------------------------------------------------
  -- reflection

  record isEpiReflecting (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field reflect-isEpi : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{f : a ⟶ b} -> isEpi (map {{of F}} f) -> isEpi f

  open isEpiReflecting {{...}} public

  --------------------------------------------------------------
  -- preservation
  record isEpiPreserving (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field preserve-isEpi : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{f : a ⟶ b} -> isEpi f -> isEpi (map {{of F}} f)

  open isEpiPreserving {{...}} public

-- //
