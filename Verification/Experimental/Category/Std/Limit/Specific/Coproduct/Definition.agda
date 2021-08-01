
module Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
-- open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where


  record isInitial (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field elim-⊥ : ∀{a} -> x ⟶ a
    field expand-⊥ : ∀{a} -> {f : x ⟶ a} -> f ∼ elim-⊥

  open isInitial {{...}} public


  record isCoproduct (a b x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field ι₀ : a ⟶ x
    field ι₁ : b ⟶ x
    field ⦗_⦘ : ∀{c} -> ((a ⟶ c) × (b ⟶ c)) -> x ⟶ c
    field {{isSetoidHom:⦗⦘}} : ∀{c} -> isSetoidHom ′((a ⟶ c) ×-𝒰 (b ⟶ c))′ ′(x ⟶ c)′ (⦗_⦘ {c})
    field reduce-ι₀ : ∀{c} {f : a ⟶ c} {g : b ⟶ c} -> ι₀ ◆ ⦗ f , g ⦘ ∼ f
    field reduce-ι₁ : ∀{c} {f : a ⟶ c} {g : b ⟶ c} -> ι₁ ◆ ⦗ f , g ⦘ ∼ g
    field expand-⊔  : ∀{c} {f : x ⟶ c} -> f ∼ ⦗ ι₀ ◆ f , ι₁ ◆ f ⦘

  open isCoproduct {{...}} public


record hasFiniteCoproducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  infixl 80 _⊔_
  field _⊔_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field {{isCoproduct:⊔}} : ∀{a b} -> isCoproduct a b (a ⊔ b)
  field ⊥ : ⟨ 𝒞 ⟩
  field {{isInitial:⊥}} : isInitial ⊥

open hasFiniteCoproducts {{...}} public



module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
  macro
    ⊔⃨ : SomeStructure
    ⊔⃨ = #structureOn (λ₋ _⊔_)

