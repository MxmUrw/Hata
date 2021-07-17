
module Verification.Experimental.Category.Std.Limit.Specific.Product where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record isTerminal (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field intro-⊤ : ∀{a} -> a ⟶ x
    field expand-⊤ : ∀{a} -> {f : a ⟶ x} -> f ∼ intro-⊤

  open isTerminal {{...}} public

  record isProduct (a b x : 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    field π₀ : x ⟶ a
    field π₁ : x ⟶ b
    field ⧼_⧽ : ∀{c} -> ((c ⟶ a) × (c ⟶ b)) -> c ⟶ x
    field {{isSetoidHom:⧼⧽}} : ∀{c} -> isSetoidHom ′((c ⟶ a) ×-𝒰 (c ⟶ b))′ ′(c ⟶ x)′ (⧼_⧽ {c})
    field reduce-π₀ : ∀{c} {f : c ⟶ a} {g : c ⟶ b} -> ⧼ f , g ⧽ ◆ π₀ ∼ f
    field reduce-π₁ : ∀{c} {f : c ⟶ a} {g : c ⟶ b} -> ⧼ f , g ⧽ ◆ π₁ ∼ g
    field expand-⊓  : ∀{c} {f : c ⟶ x} -> f ∼ ⧼ f ◆ π₀ , f ◆ π₁ ⧽

  open isProduct {{...}} public


record hasFiniteProducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  infixl 80 _⊓_
  field _⊓_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field {{isProduct:⊓}} : ∀{a b} -> isProduct a b (a ⊓ b)
  field ⊤ : ⟨ 𝒞 ⟩
  field {{isTerminal:⊤}} : isTerminal ⊤

open hasFiniteProducts {{...}} public

-- module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is Category 𝑖}} {a b x : 𝒞} {{pp : isProduct a b x }} where

--   mytest : ∀{c} -> ((c ⟶ a) × (c ⟶ b)) -> c ⟶ x
--   mytest (f , g) = ⧼ f , g ⧽



-- record hasProducts (𝒞 : Category 𝑖) : 𝒰 𝑖 where





