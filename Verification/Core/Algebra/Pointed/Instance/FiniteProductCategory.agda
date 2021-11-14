
module Verification.Core.Algebra.Pointed.Instance.FiniteProductCategory where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Algebra.Pointed.Definition
open import Verification.Core.Algebra.Pointed.Instance.Category


-- 𝐏𝐭𝐝 has products

_×-𝐏𝐭𝐝ᵘ_ : (A : 𝐏𝐭𝐝 𝑖) (B : 𝐏𝐭𝐝 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
_×-𝐏𝐭𝐝ᵘ_ A B = ⟨ A ⟩ × ⟨ B ⟩


-- module _ {A B : 𝐏𝐭𝐝 𝑖} where
module _ {Aᵘ Bᵘ : 𝒰 𝑖} {{_ : isPointed Aᵘ}} {{_ : isPointed Bᵘ}} where

  private
    macro A = #structureOn Aᵘ
    macro B = #structureOn Bᵘ

  instance
    isPointed:×-𝐏𝐭𝐝 : isPointed (A ×-𝐏𝐭𝐝ᵘ B)
    isPointed:×-𝐏𝐭𝐝 = isPointed:byDefinition (pt , pt)

  π₀-𝐏𝐭𝐝 : (A × B) ⟶ A
  π₀-𝐏𝐭𝐝 = π₀ since isPointedHom:byDefinition refl-≡

  π₁-𝐏𝐭𝐝 : (A × B) ⟶ B
  π₁-𝐏𝐭𝐝 = π₁ since isPointedHom:byDefinition refl-≡

  ⧼_⧽-𝐏𝐭𝐝 : ∀{X : 𝐏𝐭𝐝 𝑖} -> (X ⟶ A) × (X ⟶ B) -> (X ⟶ A × B)
  ⧼_⧽-𝐏𝐭𝐝 (f , g) = ⧼ ⟨ f ⟩ , ⟨ g ⟩ ⧽ since isPointedHom:byDefinition (λ i → ptmap i , ptmap i)

  instance
    isProduct:×-𝐏𝐭𝐝 : isProduct A B (A × B)
    isProduct.π₀ isProduct:×-𝐏𝐭𝐝 = π₀-𝐏𝐭𝐝
    isProduct.π₁ isProduct:×-𝐏𝐭𝐝 = π₁-𝐏𝐭𝐝
    isProduct.⧼ isProduct:×-𝐏𝐭𝐝 ⧽ = ⧼_⧽-𝐏𝐭𝐝
    isProduct.isSetoidHom:⧼⧽ isProduct:×-𝐏𝐭𝐝 = {!⧼_⧽-𝐏𝐭𝐝!}
    isProduct.reduce-π₀ isProduct:×-𝐏𝐭𝐝 = {!!}
    isProduct.reduce-π₁ isProduct:×-𝐏𝐭𝐝 = {!!}
    isProduct.expand-⊓ isProduct:×-𝐏𝐭𝐝 = {!!}

_×-𝐏𝐭𝐝_ : (A B : 𝐏𝐭𝐝 𝑖) -> 𝐏𝐭𝐝 _
_×-𝐏𝐭𝐝_ A B = A × B


