
module Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition

-- NOTE: this should actually go into "ZeroMorphismCategory"

-- 
record isZeroMorphismCategory (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field pt : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b
  field absorb-r-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> f ◆ pt {b} {c} ∼ pt {a} {c}
  field absorb-l-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : b ⟶ c} -> pt {a} {b} ◆ f ∼ pt {a} {c}

open isZeroMorphismCategory {{...}} public

module _ (𝑖 : 𝔏 ^ 3) where
  ZeroMorphismCategory = (Category 𝑖) :& isZeroMorphismCategory

  macro 𝐏𝐭𝐝𝐂𝐚𝐭 = #structureOn ZeroMorphismCategory



record Free-𝐏𝐭𝐝𝐂𝐚𝐭 (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor incl
  field ⟨_⟩ : ⟨ 𝒞 ⟩

open Free-𝐏𝐭𝐝𝐂𝐚𝐭 public


module _ {𝒞ᵘ : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞ᵘ}} where
  private
    𝒞 : Category _
    𝒞 = ′ 𝒞ᵘ ′

  data Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞) : 𝒰 (𝑗 ⌄ 0) where
    some : ⟨ a ⟩ ⟶ ⟨ b ⟩ -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b
    zero : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b

  module _ {a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} where
    data _∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ : (f g : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b) -> 𝒰 𝑗 where
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
      isSetoid:Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 = isSetoid:byDef _∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ lem-1 lem-2 lem-3

  id-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a a
  id-Free-𝐏𝐭𝐝𝐂𝐚𝐭 = some id

  _◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ : ∀{a b c : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 b c -> Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a c
  some f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 some g = some (f ◆ g)
  some f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 zero = zero
  zero ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 g = zero

  private
    lem-1 : ∀{a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b}
          -> (id-Free-𝐏𝐭𝐝𝐂𝐚𝐭 ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 f) ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 f
    lem-1 {f = some x} = some unit-l-◆
    lem-1 {f = zero} = refl

    lem-2 : ∀{a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b}
          -> (f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 id-Free-𝐏𝐭𝐝𝐂𝐚𝐭) ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 f
    lem-2 {f = some x} = some unit-r-◆
    lem-2 {f = zero} = refl

    lem-3 : ∀{a b c d : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b} {g : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 b c} {h : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 c d}
          -> ((f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 g) ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 h) ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (g ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 h))
    lem-3 {f = some x} {some x₁} {some x₂} = some assoc-l-◆
    lem-3 {f = some x} {some x₁} {zero} = refl
    lem-3 {f = some x} {zero} {h} = refl
    lem-3 {f = zero} {g} {h} = refl

    lem-4 : ∀{a b c : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ∀{f g : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b} {h i : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 b c}
          -> f ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 g -> h ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 i
          -> (f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 h) ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (g ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 i)
    lem-4 (some x) (some y) = some (x ◈ y)
    lem-4 (some x) zero = refl
    lem-4 zero q = refl

    lem-5 : ∀{a b c : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 a b}
          -> (f ◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭 zero {a = b} {b = c}) ∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 zero
    lem-5 {f = some x} = refl
    lem-5 {f = zero} = refl

  instance
    isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isCategory (Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)
    isCategory.Hom isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭
    isCategory.isSetoid:Hom isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = isSetoid:Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭
    isCategory.id isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = id-Free-𝐏𝐭𝐝𝐂𝐚𝐭
    isCategory._◆_ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = _◆-Free-𝐏𝐭𝐝𝐂𝐚𝐭_
    isCategory.unit-l-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = lem-1
    isCategory.unit-r-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = lem-2
    isCategory.unit-2-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = lem-1
    isCategory.assoc-l-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = lem-3
    isCategory.assoc-r-◆ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = lem-3 ⁻¹
    isCategory._◈_ isCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = lem-4

  instance
    isZeroMorphismCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isZeroMorphismCategory ′(Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)′
    isZeroMorphismCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = record
      { pt = zero
      ; absorb-r-◆ = lem-5
      ; absorb-l-◆ = refl
      }

  ¬isEpi:zero : ∀{a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ¬ isEpi (zero {a = a} {b})
  ¬isEpi:zero {a} {b} P = lem-p3
    where
      instance _ = P

      f g : b ⟶ b
      f = zero
      g = id

      lem-p1 : zero {a = a} ◆ f ∼ zero {a = a} ◆ g
      lem-p1 = refl

      lem-p2 : f ∼ g
      lem-p2 = cancel-epi lem-p1

      lem-p3 : 𝟘-𝒰
      lem-p3 with lem-p2
      ... | ()

  reflect-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isEpi (some f) -> isEpi f
  isEpi.cancel-epi (reflect-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 {f = f} P) {z} {g} {h} fg∼fh = lem-p3
    where
      instance _ = P

      lem-p1 : some f ◆ some g ∼ some f ◆ some h
      lem-p1 = some fg∼fh

      lem-p2 : some g ∼ some h
      lem-p2 = cancel-epi lem-p1

      lem-p3 : g ∼ h
      lem-p3 with lem-p2
      ... | some p = p

  preserve-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isEpi (f) -> isEpi (some f)
  isEpi.cancel-epi (preserve-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 P) {z} {some x} {some x₁} (some fg∼fh) = some (cancel-epi fg∼fh)
    where instance _ = P
  isEpi.cancel-epi (preserve-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 P) {z} {zero} {zero} fg∼fh = refl


instance
  hasFree:𝐂𝐚𝐭,𝐏𝐭𝐝𝐂𝐚𝐭 : hasFree (Category 𝑖) (𝐏𝐭𝐝𝐂𝐚𝐭 _)
  hasFree:𝐂𝐚𝐭,𝐏𝐭𝐝𝐂𝐚𝐭 = record { 𝑓𝑟𝑒𝑒ᵘ = λ 𝒞 -> ′ Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞 ′ }

module _ {𝒞 : Category 𝑖} {{SP : isSizedCategory 𝒞}} where
  -- private
  --   sizeC' : ∀{a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> (p : HomPair a b) -> ⟨ SizeC ⟩
  --   sizeC' (some x , g) = {!!}
  --   sizeC' (zero , some x) = {!!}
  --   sizeC' (zero , zero) = ⊥-WFT

  instance
    isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isSizedCategory ′(Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)′
    isSizedCategory.SizeO isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = SizeO {{SP}}
    isSizedCategory.sizeO isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = λ (incl x) → sizeO x

module _ {𝒞 : Category 𝑖} where
  instance
    isContradiction:zero≣some : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isContradiction (StrId {A = Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (incl a) (incl b)} (zero) (some f))
    isContradiction:zero≣some = contradiction (λ ())

    isContradiction:zero∼some : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isContradiction (_∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ {a = incl a} {b = incl b}  (zero) (some f))
    isContradiction:zero∼some = contradiction (λ ())

  cancel-injective-some-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> _∼-Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭_ {a = incl a} {b = incl b} (some f) (some g) -> f ∼ g
  cancel-injective-some-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (some x) = x



