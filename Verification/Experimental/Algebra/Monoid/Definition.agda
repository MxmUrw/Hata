
module Verification.Experimental.Algebra.Monoid.Definition where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Prop.Definition




record isMonoid {𝑗 : 𝔏 ^ 2} (A : Setoid 𝑗) : 𝒰 (𝑗) where
  field _⋆_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
        ◌ : ⟨ A ⟩
        unit-l-⋆ : ∀{a} -> ◌ ⋆ a ∼ a
        unit-r-⋆ : ∀{a} -> a ⋆ ◌ ∼ a
        assoc-l-⋆ : ∀{a b c} -> (a ⋆ b) ⋆ c ∼ a ⋆ (b ⋆ c)
        -- assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
        _`cong-⋆`_ : ∀{a₀ a₁ b₀ b₁} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆ b₀ ∼ a₁ ⋆ b₁

  assoc-r-⋆ : ∀{a b c} -> a ⋆ (b ⋆ c) ∼ (a ⋆ b) ⋆ c
  assoc-r-⋆ = assoc-l-⋆ ⁻¹
  _≀⋆≀_ = _`cong-⋆`_





  infixl 50 _⋆_ _`cong-⋆`_ _≀⋆≀_
open isMonoid {{...}} public

Monoid : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Monoid 𝑗 = Setoid 𝑗 :& isMonoid

module _ {A : 𝒰 _} {{Ap : A is Monoid 𝑖}} where
  macro
   ⋆⃨ : SomeStructure
   ⋆⃨ = #structureOn (λ₋ {A = A} {B = A} {C = A} (_⋆_))


record isCommutative {𝑗 : 𝔏 ^ 2} (A : Monoid 𝑗) : 𝒰 𝑗 where
  field comm-⋆ : ∀{a b : ⟨ A ⟩} -> a ⋆ b ∼ b ⋆ a

open isCommutative {{...}} public


record isSubmonoid {𝑗 : 𝔏 ^ 2} {A} {{_ : Monoid 𝑗 on A}} (P : 𝒫 A :& isSubsetoid) : 𝒰 𝑗 where
  field closed-◌ : ◌ ∈ P
        closed-⋆ : ∀{a b : A} -> a ∈ P -> b ∈ P -> (a ⋆ b) ∈ P
        --⟨ ⟨ P ⟩ a ⟩ -> ⟨ ⟨ P ⟩ b ⟩ -> ⟨ ⟨ P ⟩ (a ⋆ b) ⟩
open isSubmonoid {{...}} public


Submonoid : (M : Monoid 𝑖) -> 𝒰 _
Submonoid M = _ :& isSubmonoid {A = ⟨ M ⟩}



