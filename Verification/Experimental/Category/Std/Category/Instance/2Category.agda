
module Verification.Experimental.Category.Std.Category.Instance.2Category where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.AllOf.Product
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Construction.Product


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where

  ◆⃨-𝐂𝐚𝐭ᵘ : (Functor 𝒞 𝒟 × Functor 𝒟 ℰ) -> Functor 𝒞 ℰ
  ◆⃨-𝐂𝐚𝐭ᵘ = λ₋ _◆-𝐂𝐚𝐭_

  macro ◆⃨-𝐂𝐚𝐭 = #structureOn ◆⃨-𝐂𝐚𝐭ᵘ

  map-◆⃨-𝐂𝐚𝐭 : ∀{a b} -> (a ⟶ b) -> ◆⃨-𝐂𝐚𝐭 a ⟶ ◆⃨-𝐂𝐚𝐭 b
  map-◆⃨-𝐂𝐚𝐭 {f₀ , g₀} {f₁ , g₁} (α , β) = γ since isNatural:γ
    where
      γ : ∀{x : ⟨ 𝒞 ⟩} -> ⟨ (f₀ ◆-𝐂𝐚𝐭 g₀) ⟩ x ⟶ ⟨ (f₁ ◆-𝐂𝐚𝐭 g₁) ⟩ x
      γ {x} = ⟨ β ⟩ ◆ map ⟨ α ⟩

      isNatural:γ : isNatural (f₀ ◆-𝐂𝐚𝐭 g₀) (f₁ ◆-𝐂𝐚𝐭 g₁) γ
      isNatural:γ = {!!}

  instance
    isFunctor:◆⃨-𝐂𝐚𝐭 : isFunctor (𝐅𝐮𝐧𝐜 𝒞 𝒟 ×-𝐂𝐚𝐭 𝐅𝐮𝐧𝐜 𝒟 ℰ) (𝐅𝐮𝐧𝐜 𝒞 ℰ) ◆⃨-𝐂𝐚𝐭
    isFunctor.map isFunctor:◆⃨-𝐂𝐚𝐭 = map-◆⃨-𝐂𝐚𝐭
    isFunctor.isSetoidHom:map isFunctor:◆⃨-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-id isFunctor:◆⃨-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-◆ isFunctor:◆⃨-𝐂𝐚𝐭 = {!!}

  _⇃◆⇂_ : ∀{f₀ f₁ : Functor 𝒞 𝒟} {g₀ g₁ : Functor 𝒟 ℰ}
        -> (α : Natural f₀ f₁) -> (β : Natural g₀ g₁)
        -> (Natural (f₀ ◆-𝐂𝐚𝐭 g₀) (f₁ ◆-𝐂𝐚𝐭 g₁))
  _⇃◆⇂_ α β = map-◆⃨-𝐂𝐚𝐭 (α , β)



  -- module _ {p : Functor 𝒞 𝒟} where
      -- instance
      --   isFunctor:◆-Cat : isFunctor ′(Functor 𝒟 ℰ)′ ′(Functor 𝒞 ℰ)′ (p ◆-𝐂𝐚𝐭_)
      --   isFunctor.map isFunctor:◆-Cat F = {!!}
      --   isFunctor.isSetoidHom:map isFunctor:◆-Cat = {!!}
      --   isFunctor.functoriality-id isFunctor:◆-Cat = {!!}
      --   isFunctor.functoriality-◆ isFunctor:◆-Cat = {!!}





