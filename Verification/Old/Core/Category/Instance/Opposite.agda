
module Verification.Old.Core.Category.Instance.Opposite where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition

-- | For a more general kind of example, consider an arbitrary category |𝒞|.
--   Then we can construct another category |𝒞 ᵒᵖ| which has the same objects
--   as |𝒞|, but where the direction of all arrows is reversed.

-- [Definition]
-- | There is a function [..], mapping a category to its opposite. It is defined as:
_ᵒᵖ : Category 𝑖 -> Category 𝑖
⟨ 𝒞 ᵒᵖ ⟩                         = ⟨ 𝒞 ⟩
isCategory.Hom (of 𝒞 ᵒᵖ) a b  = Hom {{of 𝒞}} b a

-- |> All equations for |𝒞 ᵒᵖ| can be proven by simply using their symmetric counterpart in $𝒞$.
isCategory._≣_        (of 𝒞 ᵒᵖ)  = _≣_
isCategory.isEquivRel:≣   (of 𝒞 ᵒᵖ)  = isEquivRel:≣
isCategory.id         (of 𝒞 ᵒᵖ)  = id
isCategory._◆_        (of 𝒞 ᵒᵖ)  = λ f g -> g ◆ f
isCategory._◈_        (of 𝒞 ᵒᵖ)  = λ p q -> q ◈ p
isCategory.unit-l-◆   (of 𝒞 ᵒᵖ)  = unit-r-◆
isCategory.unit-r-◆   (of 𝒞 ᵒᵖ)  = unit-l-◆
isCategory.unit-2-◆   (of 𝒞 ᵒᵖ)  = unit-2-◆
isCategory.assoc-l-◆  (of 𝒞 ᵒᵖ)  = assoc-r-◆
isCategory.assoc-r-◆  (of 𝒞 ᵒᵖ)  = assoc-l-◆
-- //
