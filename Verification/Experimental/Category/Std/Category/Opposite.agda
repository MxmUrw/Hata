
module Verification.Experimental.Category.Std.Category.Opposite where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition


-- | For a more general kind of example, consider an arbitrary category |𝒞|.
--   Then we can construct another category |𝒞 ᵒᵖ| which has the same objects
--   as |𝒞|, but where the direction of all arrows is reversed.

-- [Definition]
-- | There is a function [..], mapping a category to its opposite. It is defined as:
_ᵒᵖ : Category 𝑖 -> Category 𝑖
_ᵒᵖ 𝒞 = ′ ⟨ 𝒞 ⟩ ′ {{Op}}
  where Op : isCategory ⟨ 𝒞 ⟩
        isCategory.Hom Op a b = Hom b a
        isCategory.isSetoid:Hom Op = isSetoid:Hom {{of 𝒞}}
        isCategory.id Op = id
        isCategory._◆_ Op f g = g ◆ f
        isCategory.unit-l-◆ Op = unit-r-◆
        isCategory.unit-r-◆ Op    = unit-l-◆       -- incl ⟨ unit-l-◆ ⟩
        isCategory.unit-2-◆ Op    = unit-2-◆       -- incl ⟨ unit-2-◆ ⟩
        isCategory.assoc-l-◆ Op   = assoc-r-◆      -- incl ⟨ assoc-r-◆ ⟩
        isCategory.assoc-r-◆ Op   = assoc-l-◆      -- incl ⟨ assoc-l-◆ ⟩
        isCategory._◈_ Op (p) (q) = q ◈ p -- incl ⟨ incl q ◈ incl p ⟩

module _ {𝒞 : Category 𝑖} where
  ᵒᵖᵒᵖ : (𝒞 ᵒᵖ ᵒᵖ) ≡-Str 𝒞
  ᵒᵖᵒᵖ = refl-≣

-- ⟨ 𝒞 ᵒᵖ ⟩                         = ⟨ 𝒞 ⟩
-- isCategory.Hom' (of 𝒞 ᵒᵖ) a b  = Hom' {{of 𝒞}} b a

-- |> All equations for |𝒞 ᵒᵖ| can be proven by simply using their symmetric counterpart in $𝒞$.
-- isCategory._≣_        (of 𝒞 ᵒᵖ)  = _≣_
-- isCategory.isEquivRel:≣   (of 𝒞 ᵒᵖ)  = isEquivRel:≣
-- isCategory.id         (of 𝒞 ᵒᵖ)  = id
-- isCategory._◆_        (of 𝒞 ᵒᵖ)  = λ f g -> g ◆ f
-- isCategory._◈_        (of 𝒞 ᵒᵖ)  = λ p q -> q ◈ p
-- isCategory.unit-l-◆   (of 𝒞 ᵒᵖ)  = unit-r-◆
-- isCategory.unit-r-◆   (of 𝒞 ᵒᵖ)  = unit-l-◆
-- isCategory.unit-2-◆   (of 𝒞 ᵒᵖ)  = unit-2-◆
-- isCategory.assoc-l-◆  (of 𝒞 ᵒᵖ)  = assoc-r-◆
-- isCategory.assoc-r-◆  (of 𝒞 ᵒᵖ)  = assoc-l-◆
-- //

