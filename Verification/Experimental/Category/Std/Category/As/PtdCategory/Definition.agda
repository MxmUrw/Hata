
module Verification.Experimental.Category.Std.Category.As.PtdCategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition

record isPtdCategory (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field pt : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b

open isPtdCategory {{...}} public

module _ (𝑖 : 𝔏 ^ 3) where
  PtdCategory = (Category 𝑖) :& isPtdCategory

  macro 𝐏𝐭𝐝𝐂𝐚𝐭 = #structureOn PtdCategory



record Free-𝐏𝐭𝐝𝐂𝐚𝐭 (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor incl
  field ⟨_⟩ : ⟨ 𝒞 ⟩

open Free-𝐏𝐭𝐝𝐂𝐚𝐭 public


module _ {𝒞 : Category 𝑖} where
  data Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞) : 𝒰 (𝑖 ⌄ 1) where
    some : ⟨ a ⟩ ⟶ ⟨ b ⟩ -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b
    zero : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b

  module _ {a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} where
    data _∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ : (f g : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b) -> 𝒰 (𝑖 ⌄ 1 ､ 𝑖 ⌄ 2) where
      some : ∀{f g} -> f ∼ g -> some f ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 some g
      zero : zero ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 zero

    private
      lem-1 : ∀{f : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b} -> f ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 f
      lem-1 {some x} = some refl
      lem-1 {zero} = zero

      lem-2 : ∀{f g : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b} -> f ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 g -> g ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 f
      lem-2 (some x) = some (x ⁻¹)
      lem-2 zero = zero

      lem-3 : ∀{f g h : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b} -> f ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 g -> g ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 h -> f ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 h
      lem-3 (some x) (some y) = some (x ∙ y)
      lem-3 zero zero = zero

    instance
      isSetoid:Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isSetoid (Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b)
      isSetoid:Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 = setoid _∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ lem-1 lem-2 lem-3

  id-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a a
  id-Free-𝐏𝐭𝐝𝐂𝐚𝐭 = some id

  _◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ : ∀{a b c : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 b c -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a c
  some f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 some g = some (f ◆ g)
  some f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 zero = zero
  zero ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 g = zero

  instance
    isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isCategory (Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)
    isCategory.Hom isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭
    isCategory.isSetoid:Hom isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = isSetoid:Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭
    isCategory.id isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = id-Free-𝐏𝐭𝐝𝐂𝐚𝐭
    isCategory._◆_ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = _◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭_
    isCategory.unit-l-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isCategory.unit-r-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isCategory.unit-2-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isCategory.assoc-l-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isCategory.assoc-r-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isCategory._◈_ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}

  instance
    isPtdCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isPtdCategory ′(Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)′
    isPtdCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = record { pt = zero }



instance
  hasFree:𝐂𝐚𝐭,𝐏𝐭𝐝𝐂𝐚𝐭 : hasFree (Category 𝑖) (𝐏𝐭𝐝𝐂𝐚𝐭 _)
  hasFree:𝐂𝐚𝐭,𝐏𝐭𝐝𝐂𝐚𝐭 = record { 𝑓𝑟𝑒𝑒ᵘ = λ 𝒞 -> ′ Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞 ′ }


