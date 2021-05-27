
module Verification.Core.Category.Instance.Cat.Products where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
-- open import Verification.Core.Category.Functor.Adjunction
-- open import Verification.Core.Category.Limit.Kan.Definition
-- open import Verification.Core.Category.Limit.Kan.Terminal
-- open import Verification.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Core.Category.Limit.Kan.Product
-- open import Verification.Core.Category.Instance.Type
-- open import Verification.Core.Category.Instance.Cat
-- open import Verification.Core.Category.Instance.SmallCategories
-- open import Verification.Core.Category.FreeCategory
-- open import Verification.Core.Category.Quiver
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Category.Lift
open import Verification.Core.Homotopy.Level
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.Instance.Level
open import Verification.Core.Order.Instance.Product

open import Verification.Core.Category.Instance.Cat.Definition
-- open import Verification.Core.Category.Instance.Set.Products


_×-Cat_ : Category 𝑖 -> Category 𝑗 -> Category (𝑖 ∨ 𝑗)
⟨ 𝒞 ×-Cat 𝒟 ⟩ = ⟨ 𝒞 ⟩ ×-𝒰 ⟨ 𝒟 ⟩
isCategory.Hom (of (𝒞 ×-Cat 𝒟)) (a₁ , a₂) (b₁ , b₂) = a₁ ⟶ b₁ ×-𝒰 a₂ ⟶ b₂
isCategory._≣_ (of (𝒞 ×-Cat 𝒟)) (f₁ , f₂) (g₁ , g₂) = (f₁ ≣ g₁) ×-𝒰 (f₂ ≣ g₂)
isCategory.isEquivRel:≣ (of (𝒞 ×-Cat 𝒟)) = {!!}
isCategory.id (of (𝒞 ×-Cat 𝒟)) = (id , id)
isCategory._◆_ (of (𝒞 ×-Cat 𝒟)) (f₁ , f₂) (g₁ , g₂) = (f₁ ◆ g₁ , f₂ ◆ g₂)
isCategory.unit-l-◆ (of (𝒞 ×-Cat 𝒟)) = {!!}
isCategory.unit-r-◆ (of (𝒞 ×-Cat 𝒟)) = {!!}
isCategory.unit-2-◆ (of (𝒞 ×-Cat 𝒟)) = {!!}
isCategory.assoc-l-◆ (of (𝒞 ×-Cat 𝒟)) = {!!}
isCategory.assoc-r-◆ (of (𝒞 ×-Cat 𝒟)) = {!!}
isCategory._◈_ (of (𝒞 ×-Cat 𝒟)) = {!!}

