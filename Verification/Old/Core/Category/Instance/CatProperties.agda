
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.VHM3.Old.Core.Category.Instance.CatProperties where

open import Verification.VHM3.Old.Core.Base
open import Verification.VHM3.Old.Core.Meta
open import Verification.VHM3.Old.Core.Category.Base
open import Verification.VHM3.Old.Core.Category.Limit
open import Verification.VHM3.Old.Core.Category.Monad
open import Verification.VHM3.Old.Core.Category.Instance.Type
open import Verification.VHM3.Old.Core.Category.Instance.Cat

_×-Category_ : Category 𝑖𝑖𝑖 -> Category 𝑗𝑗𝑗 -> Category (zipL 𝑖𝑖𝑖 𝑗𝑗𝑗)
⟨ X ×-Category Y ⟩ = ⟨ X ⟩ ×-𝒰 ⟨ Y ⟩
ICategory.Hom (of (X ×-Category Y)) (a1 , a2) (b1 , b2) = Hom a1 b1 ×-𝒰 Hom a2 b2
ICategory._≣_ (of (X ×-Category Y)) (f1 , g1) (f2 , g2) = (f1 ≣ f2) ×-𝒰 (g1 ≣ g2)
ICategory.IEquiv:≣ (of (X ×-Category Y)) = {!!}
ICategory.id (of (X ×-Category Y)) = id , id
ICategory._◆_ (of (X ×-Category Y)) (f1 , g1) (f2 , g2) = (f1 ◆ f2) , (g1 ◆ g2)
ICategory._◈_ (of (X ×-Category Y)) = {!!}
ICategory./id◆ (of (X ×-Category Y)) = {!!}
ICategory./◆id (of (X ×-Category Y)) = {!!}
ICategory./id₂ (of (X ×-Category Y)) = {!!}
ICategory./◆◆ₗ (of (X ×-Category Y)) = {!!}
ICategory./◆◆ᵣ (of (X ×-Category Y)) = {!!}

hasProducts:Category : hasProducts (Category 𝑖𝑖𝑖)
⟨ ⟨ has_ShapedLimits.lim hasProducts:Category D ⟩ ⟩ = ⟨ D ⟩ ₀ ×-Category ⟨ D ⟩ ₁
of ⟨ has_ShapedLimits.lim hasProducts:Category D ⟩ = {!!}
of (has_ShapedLimits.lim hasProducts:Category D) = {!!}


