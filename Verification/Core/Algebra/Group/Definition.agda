
module Verification.Core.Algebra.Group.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition


record isGroup {𝑗 : 𝔏 ^ 2} (A : Monoid 𝑗) : 𝒰 𝑗 where
  field ◡_ : ⟨ A ⟩ -> ⟨ A ⟩
        inv-l-⋆ : ∀{a} -> ◡ a ⋆ a ∼ ◌
        inv-r-⋆ : ∀{a} -> a ⋆ ◡ a ∼ ◌
        cong-◡_ : ∀{a₀ a₁} -> a₀ ∼ a₁ -> ◡ a₀ ∼ ◡ a₁
  ◡≀_ = cong-◡_
  infix 100 ◡_ ◡≀_
open isGroup {{...}} public

Group : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Group 𝑗 = Monoid 𝑗 :& isGroup


record isSubgroup {𝑗 : 𝔏 ^ 2} {A} {{_ : Group 𝑗 on A}} (P : 𝒫 A :& isSubsetoid :& isSubmonoid) : 𝒰 𝑗 where
  field closed-◡ : ∀{a} -> ⟨ ⟨ P ⟩ a ⟩ -> ⟨ ⟨ P ⟩ (◡ a) ⟩
open isSubgroup {{...}} public


Subgroup : (G : Group 𝑗) -> 𝒰 _
Subgroup G = 𝒫 ⟨ G ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup


data RelSubgroup {𝑗 : 𝔏 ^ 2} {G : Group 𝑗} (H : Subgroup G) (a : ⟨ G ⟩) (b : ⟨ G ⟩) : 𝒰 (𝑗 ⌄ 0) where
  incl : ⟨ ⟨ H ⟩ (a ⋆ ◡ b) ⟩ -> RelSubgroup H a b


module _ {𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} {{_ : Group (𝑖 , 𝑗) on A}} where
  cancel-⋆-l : ∀{a b c : A} -> a ⋆ b ∼ a ⋆ c -> b ∼ c
  cancel-⋆-l {a} {b} {c} p =
      b             ≣⟨ unit-l-⋆ ⁻¹ ⟩
      ◌ ⋆ b         ≣⟨ inv-l-⋆ ⁻¹ ≀⋆≀ refl ⟩
      (◡ a ⋆ a) ⋆ b ≣⟨ assoc-l-⋆ ⟩
      ◡ a ⋆ (a ⋆ b) ≣⟨ refl ≀⋆≀ p ⟩
      ◡ a ⋆ (a ⋆ c) ≣⟨ assoc-r-⋆ ⟩
      (◡ a ⋆ a) ⋆ c ≣⟨ inv-l-⋆ ≀⋆≀ refl ⟩
      ◌ ⋆ c         ≣⟨ unit-l-⋆ ⟩
      c             ∎

  distr-⋆-◡ : ∀{a b : A} -> ◡ (a ⋆ b) ∼ ◡ b ⋆ ◡ a
  distr-⋆-◡ {a} {b} = cancel-⋆-l $
    (a ⋆ b) ⋆ ◡ (a ⋆ b)   ≣⟨ inv-r-⋆ ⟩
    ◌                     ≣⟨ inv-r-⋆ ⁻¹ ⟩
    a ⋆ ◡ a               ≣⟨ unit-r-⋆ ⁻¹ ≀⋆≀ refl ⟩
    (a ⋆ ◌) ⋆ ◡ a         ≣⟨ (refl ≀⋆≀ inv-r-⋆ ⁻¹) ≀⋆≀ refl ⟩
    (a ⋆ (b ⋆ ◡ b)) ⋆ ◡ a ≣⟨ assoc-r-⋆ ≀⋆≀ refl ⟩
    ((a ⋆ b) ⋆ ◡ b) ⋆ ◡ a ≣⟨ assoc-l-⋆ ⟩
    (a ⋆ b) ⋆ (◡ b ⋆ ◡ a) ∎

  double-◡ : ∀{a : A} -> ◡ ◡ a ∼ a
  double-◡ {a} = cancel-⋆-l $
    ◡ a ⋆ ◡ ◡ a ≣⟨ inv-r-⋆ ⟩
    ◌           ≣⟨ inv-l-⋆ ⁻¹ ⟩
    ◡ a ⋆ a     ∎

  unique-inverse-⋆-r : ∀{a b : A} -> a ⋆ b ∼ ◌ -> ◡ a ∼ b
  unique-inverse-⋆-r {a} {b} p =
    let P₀ : a ⋆ b ∼ a ⋆ ◡ a
        P₀ = a ⋆ b   ≣⟨ p ⟩
             ◌       ≣⟨ inv-r-⋆ ⁻¹ ⟩
             a ⋆ ◡ a ∎
    in sym (cancel-⋆-l P₀)

  reduce-◡◌ : ◡ ◌ ∼ ◌
  reduce-◡◌ = ◡ ◌     ≣⟨ unit-r-⋆ ⁻¹ ⟩
              ◡ ◌ ⋆ ◌ ≣⟨ inv-l-⋆ ⟩
              ◌       ∎




