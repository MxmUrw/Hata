
module Verification.Experimental.Category.Std.Category.As.PtdCategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Sized.Definition
open import Verification.Experimental.Category.Std.Morphism.Epi.Definition

record isPtdCategory (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field pt : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b
  field absorb-r-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> f ◆ pt {b} {c} ∼ pt {a} {c}
  field absorb-l-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : b ⟶ c} -> pt {a} {b} ◆ f ∼ pt {a} {c}

open isPtdCategory {{...}} public

module _ (𝑖 : 𝔏 ^ 3) where
  PtdCategory = (Category 𝑖) :& isPtdCategory

  macro 𝐏𝐭𝐝𝐂𝐚𝐭 = #structureOn PtdCategory



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
    isPtdCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = record
      { pt = zero
      ; absorb-r-◆ = {!!}
      ; absorb-l-◆ = refl
      }

  ¬isEpi:zero : ∀{a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> ¬ isEpi (zero {a = a} {b})
  ¬isEpi:zero {a} {b} P = lem-3
    where
      instance _ = P

      f g : b ⟶ b
      f = zero
      g = id

      lem-1 : zero {a = a} ◆ f ∼ zero {a = a} ◆ g
      lem-1 = refl

      lem-2 : f ∼ g
      lem-2 = cancel-epi lem-1

      lem-3 : 𝟘-𝒰
      lem-3 with lem-2
      ... | ()

  reflect-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isEpi (some f) -> isEpi f
  isEpi.cancel-epi (reflect-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 {f = f} P) {z} {g} {h} fg∼fh = lem-3
    where
      instance _ = P

      lem-1 : some f ◆ some g ∼ some f ◆ some h
      lem-1 = some fg∼fh

      lem-2 : some g ∼ some h
      lem-2 = cancel-epi lem-1

      lem-3 : g ∼ h
      lem-3 with lem-2
      ... | some p = p

  preserve-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isEpi (f) -> isEpi (some f)
  isEpi.cancel-epi (preserve-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 P) {z} {some x} {some x₁} (some fg∼fh) = some (cancel-epi fg∼fh)
    where instance _ = P
  isEpi.cancel-epi (preserve-isEpi-Free-𝐏𝐭𝐝𝐂𝐚𝐭 P) {z} {zero} {zero} fg∼fh = refl


instance
  hasFree:𝐂𝐚𝐭,𝐏𝐭𝐝𝐂𝐚𝐭 : hasFree (Category 𝑖) (𝐏𝐭𝐝𝐂𝐚𝐭 _)
  hasFree:𝐂𝐚𝐭,𝐏𝐭𝐝𝐂𝐚𝐭 = record { 𝑓𝑟𝑒𝑒ᵘ = λ 𝒞 -> ′ Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞 ′ }

module _ {𝒞 : Category 𝑖} {{SP : isSizedCategory 𝒞}} where
  private
    sizeC' : ∀{a b : Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞} -> (p : HomPair a b) -> ⟨ SizeC ⟩
    sizeC' (some x , g) = {!!}
    sizeC' (zero , some x) = {!!}
    sizeC' (zero , zero) = ⊥-WFT

  instance
    isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 : isSizedCategory ′(Free-𝐏𝐭𝐝𝐂𝐚𝐭 𝒞)′
    isSizedCategory.isDiscrete:this isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isSizedCategory.isSet-Str:this isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = {!!}
    isSizedCategory.SizeC isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = SizeC {{SP}}
    isSizedCategory.sizeC isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = sizeC'
    isSizedCategory.SizeO isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = SizeO {{SP}}
    isSizedCategory.sizeO isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 = λ (incl x) → sizeO x
    isSizedCategory.cong-sizeC isSizedCategory:Free-𝐏𝐭𝐝𝐂𝐚𝐭 f g x = {!!}

module _ {𝒞 : Category 𝑖} where
  instance
    isContradiction:zero≣some : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isContradiction (StrId {A = Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (incl a) (incl b)} (zero) (some f))
    isContradiction:zero≣some = contradiction (λ ())

  cancel-injective-some-Free-𝐏𝐭𝐝𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> StrId {A = Hom-Free-𝐏𝐭𝐝𝐂𝐚𝐭 (incl a) (incl b)} (some f) (some g) -> f ≣ g
  cancel-injective-some-Free-𝐏𝐭𝐝𝐂𝐚𝐭 refl-≣ = refl-≣

