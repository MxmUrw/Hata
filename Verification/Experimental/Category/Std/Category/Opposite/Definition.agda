
module Verification.Experimental.Category.Std.Category.Opposite.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition



record _ᵒᵖ⌯ᵘ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : A

open _ᵒᵖ⌯ᵘ public

macro
  _ᵒᵖ⌯ : ∀{𝑖 : 𝔏} {𝑙 : 𝔏 ^ 2} -> (𝒰' 𝑖) [ 𝑙 ]→ SomeStructure
  _ᵒᵖ⌯ = λstr A ↦ #structureOn (A ᵒᵖ⌯ᵘ)


module _ {𝒞 : 𝒰 𝑖} {{𝒞P : isCategory {𝑗} 𝒞}} where
  record Hom-ᵒᵖ⌯ (a b : 𝒞 ᵒᵖ⌯ᵘ) : 𝒰 (𝑗 ⌄ 0) where
    constructor incl
    field ⟨_⟩ : ⟨ b ⟩ ⟶ ⟨ a ⟩

  open Hom-ᵒᵖ⌯ public

  module _ {a b : 𝒞 ᵒᵖ⌯ᵘ} where
    -- _∼-Hom-ᵒᵖ⌯_ : (f g : Hom-ᵒᵖ⌯ a b) -> 𝒰 _
    -- _∼-Hom-ᵒᵖ⌯_ f g = ⟨ f ⟩ ∼ ⟨ g ⟩

    record _∼-Hom-ᵒᵖ⌯_ (f g : Hom-ᵒᵖ⌯ a b) : 𝒰 (𝑗 ⌄ 1) where
      field ⟨_⟩ : ⟨ f ⟩ ∼ ⟨ g ⟩

    -- instance
    isSetoid:Hom-ᵒᵖ⌯ : isSetoid (Hom-ᵒᵖ⌯ a b)
    isSetoid:Hom-ᵒᵖ⌯ = setoid _∼-Hom-ᵒᵖ⌯_ {!!} {!!} {!!}

  id-ᵒᵖ⌯ : ∀{a : 𝒞 ᵒᵖ⌯ᵘ} -> Hom-ᵒᵖ⌯ a a
  id-ᵒᵖ⌯ = {!!}

  instance
    isCategory:ᵒᵖ⌯ : isCategory (𝒞 ᵒᵖ⌯)
    isCategory.Hom isCategory:ᵒᵖ⌯ = Hom-ᵒᵖ⌯
    -- λ a b -> Hom ⟨ b ⟩ ⟨ a ⟩
    isCategory.isSetoid:Hom isCategory:ᵒᵖ⌯ = isSetoid:Hom-ᵒᵖ⌯
    isCategory.id isCategory:ᵒᵖ⌯ = id-ᵒᵖ⌯
    isCategory._◆_ isCategory:ᵒᵖ⌯ = λ f g -> incl (⟨ g ⟩ ◆ ⟨ f ⟩)
    isCategory.unit-l-◆ isCategory:ᵒᵖ⌯  = {!!} -- unit-r-◆
    isCategory.unit-r-◆ isCategory:ᵒᵖ⌯  = {!!} -- unit-l-◆
    isCategory.unit-2-◆ isCategory:ᵒᵖ⌯  = {!!} -- unit-2-◆ {{𝒞P}}
    isCategory.assoc-l-◆ isCategory:ᵒᵖ⌯ = {!!} -- assoc-r-◆
    isCategory.assoc-r-◆ isCategory:ᵒᵖ⌯ = {!!} -- assoc-l-◆
    isCategory._◈_ isCategory:ᵒᵖ⌯ = {!!}
{-
-}


-- -- [Definition]
-- _ᵒᵖ : Category 𝑖 -> Category 𝑖
-- _ᵒᵖ 𝒞 = ′ ⟨ 𝒞 ⟩ ′ {{Op}}
--   where Op : isCategory ⟨ 𝒞 ⟩
--         isCategory.Hom Op a b = Hom b a
--         isCategory.isSetoid:Hom Op = isSetoid:Hom {{of 𝒞}}
--         isCategory.id Op = id
--         isCategory._◆_ Op f g = g ◆ f
--         isCategory.unit-l-◆ Op = unit-r-◆
--         isCategory.unit-r-◆ Op    = unit-l-◆       -- incl ⟨ unit-l-◆ ⟩
--         isCategory.unit-2-◆ Op    = unit-2-◆       -- incl ⟨ unit-2-◆ ⟩
--         isCategory.assoc-l-◆ Op   = assoc-r-◆      -- incl ⟨ assoc-r-◆ ⟩
--         isCategory.assoc-r-◆ Op   = assoc-l-◆      -- incl ⟨ assoc-l-◆ ⟩
--         isCategory._◈_ Op (p) (q) = q ◈ p -- incl ⟨ incl q ◈ incl p ⟩

-- module _ {𝒞 : Category 𝑖} where
--   ᵒᵖᵒᵖ : (𝒞 ᵒᵖ ᵒᵖ) ≡-Str 𝒞
--   ᵒᵖᵒᵖ = refl-≣
