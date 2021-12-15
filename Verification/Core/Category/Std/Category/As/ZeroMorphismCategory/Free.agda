
module Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Free where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition

open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition

-- [Definition]
-- | Let |𝒞| be a category. We define |Free-𝐙𝐌𝐂𝐚𝐭 𝒞| as the category obtained
--   from |𝒞| by freely adjoining an additional arrow to each hom-set.
--   This is done by defining each hom-set of |Free-𝐙𝐌𝐂𝐚𝐭 𝒞| by a data type
--   with two constructors:
-- | - One which includes arrows from |𝒞| into |Free-𝐙𝐌𝐂𝐚𝐭 𝒞|, namely |some : ⟨ a ⟩ ⟶ ⟨ b ⟩ → Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b|
-- | - And one which describes failure: |zero : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b|
-- |: This could have been done using the |Maybe| data type,
--    but as usual, dedicated data types are used for
--    better type inference.

-- //

-- [Lemma]
-- | There is indeed the structure of a category on |Free-𝐙𝐌𝐂𝐚𝐭 𝒞|
--   which makes it into a category with zero morphisms,
--   with |0 = zero|

-- //

-- [Proof]
-- | The implementation of this structure is not difficult,
--   rather an exercise in many case distinctions
--   between |zero| and |some|.

-- //

-- [Hide]
record Free-𝐙𝐌𝐂𝐚𝐭 (𝒞 : Category 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor incl
  field ⟨_⟩ : ⟨ 𝒞 ⟩

open Free-𝐙𝐌𝐂𝐚𝐭 public


module _ {𝒞ᵘ : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞ᵘ}} where
  private
    𝒞 : Category _
    𝒞 = ′ 𝒞ᵘ ′

  data Hom-Free-𝐙𝐌𝐂𝐚𝐭 (a b : Free-𝐙𝐌𝐂𝐚𝐭 𝒞) : 𝒰 (𝑗 ⌄ 0) where
    some : ⟨ a ⟩ ⟶ ⟨ b ⟩ -> Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b
    zero : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b

  module _ {a b : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} where
    data _∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭_ : (f g : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b) -> 𝒰 𝑗 where
      some : ∀{f g} -> f ∼ g -> some f ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 some g
      zero : zero ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 zero

    private
      lem-1 : ∀{f : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b} -> f ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 f
      lem-1 {some x} = some refl
      lem-1 {zero} = zero

      lem-2 : ∀{f g : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b} -> f ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 g -> g ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 f
      lem-2 (some x) = some (x ⁻¹)
      lem-2 zero = zero

      lem-3 : ∀{f g h : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b} -> f ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 g -> g ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 h -> f ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 h
      lem-3 (some x) (some y) = some (x ∙ y)
      lem-3 zero zero = zero

    instance
      isSetoid:Hom-Free-𝐙𝐌𝐂𝐚𝐭 : isSetoid (Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b)
      isSetoid:Hom-Free-𝐙𝐌𝐂𝐚𝐭 = isSetoid:byDef _∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭_ lem-1 lem-2 lem-3

  id-Free-𝐙𝐌𝐂𝐚𝐭 : ∀{a : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> Hom-Free-𝐙𝐌𝐂𝐚𝐭 a a
  id-Free-𝐙𝐌𝐂𝐚𝐭 = some id

  _◆-Free-𝐙𝐌𝐂𝐚𝐭_ : ∀{a b c : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b -> Hom-Free-𝐙𝐌𝐂𝐚𝐭 b c -> Hom-Free-𝐙𝐌𝐂𝐚𝐭 a c
  some f ◆-Free-𝐙𝐌𝐂𝐚𝐭 some g = some (f ◆ g)
  some f ◆-Free-𝐙𝐌𝐂𝐚𝐭 zero = zero
  zero ◆-Free-𝐙𝐌𝐂𝐚𝐭 g = zero

  private
    lem-1 : ∀{a b : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b}
          -> (id-Free-𝐙𝐌𝐂𝐚𝐭 ◆-Free-𝐙𝐌𝐂𝐚𝐭 f) ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 f
    lem-1 {f = some x} = some unit-l-◆
    lem-1 {f = zero} = refl

    lem-2 : ∀{a b : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b}
          -> (f ◆-Free-𝐙𝐌𝐂𝐚𝐭 id-Free-𝐙𝐌𝐂𝐚𝐭) ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 f
    lem-2 {f = some x} = some unit-r-◆
    lem-2 {f = zero} = refl

    lem-3 : ∀{a b c d : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b} {g : Hom-Free-𝐙𝐌𝐂𝐚𝐭 b c} {h : Hom-Free-𝐙𝐌𝐂𝐚𝐭 c d}
          -> ((f ◆-Free-𝐙𝐌𝐂𝐚𝐭 g) ◆-Free-𝐙𝐌𝐂𝐚𝐭 h) ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 (f ◆-Free-𝐙𝐌𝐂𝐚𝐭 (g ◆-Free-𝐙𝐌𝐂𝐚𝐭 h))
    lem-3 {f = some x} {some x₁} {some x₂} = some assoc-l-◆
    lem-3 {f = some x} {some x₁} {zero} = refl
    lem-3 {f = some x} {zero} {h} = refl
    lem-3 {f = zero} {g} {h} = refl

    lem-4 : ∀{a b c : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> ∀{f g : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b} {h i : Hom-Free-𝐙𝐌𝐂𝐚𝐭 b c}
          -> f ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 g -> h ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 i
          -> (f ◆-Free-𝐙𝐌𝐂𝐚𝐭 h) ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 (g ◆-Free-𝐙𝐌𝐂𝐚𝐭 i)
    lem-4 (some x) (some y) = some (x ◈ y)
    lem-4 (some x) zero = refl
    lem-4 zero q = refl

    lem-5 : ∀{a b c : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> ∀{f : Hom-Free-𝐙𝐌𝐂𝐚𝐭 a b}
          -> (f ◆-Free-𝐙𝐌𝐂𝐚𝐭 zero {a = b} {b = c}) ∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭 zero
    lem-5 {f = some x} = refl
    lem-5 {f = zero} = refl

  instance
    isCategory:Free-𝐙𝐌𝐂𝐚𝐭 : isCategory (Free-𝐙𝐌𝐂𝐚𝐭 𝒞)
    isCategory.Hom isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = Hom-Free-𝐙𝐌𝐂𝐚𝐭
    isCategory.isSetoid:Hom isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = isSetoid:Hom-Free-𝐙𝐌𝐂𝐚𝐭
    isCategory.id isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = id-Free-𝐙𝐌𝐂𝐚𝐭
    isCategory._◆_ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = _◆-Free-𝐙𝐌𝐂𝐚𝐭_
    isCategory.unit-l-◆ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = lem-1
    isCategory.unit-r-◆ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = lem-2
    isCategory.unit-2-◆ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = lem-1
    isCategory.assoc-l-◆ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = lem-3
    isCategory.assoc-r-◆ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = lem-3 ⁻¹
    isCategory._◈_ isCategory:Free-𝐙𝐌𝐂𝐚𝐭 = lem-4

  instance
    isZeroMorphismCategory:Free-𝐙𝐌𝐂𝐚𝐭 : isZeroMorphismCategory ′(Free-𝐙𝐌𝐂𝐚𝐭 𝒞)′
    isZeroMorphismCategory:Free-𝐙𝐌𝐂𝐚𝐭 = record
      { pt = zero
      ; absorb-r-◆ = lem-5
      ; absorb-l-◆ = refl
      }

  ¬isEpi:zero : ∀{a b : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> ¬ isEpi (zero {a = a} {b})
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

  reflect-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isEpi (some f) -> isEpi f
  isEpi.cancel-epi (reflect-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 {f = f} P) {z} {g} {h} fg∼fh = lem-p3
    where
      instance _ = P

      lem-p1 : some f ◆ some g ∼ some f ◆ some h
      lem-p1 = some fg∼fh

      lem-p2 : some g ∼ some h
      lem-p2 = cancel-epi lem-p1

      lem-p3 : g ∼ h
      lem-p3 with lem-p2
      ... | some p = p

  preserve-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isEpi (f) -> isEpi (some f)
  isEpi.cancel-epi (preserve-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 P) {z} {some x} {some x₁} (some fg∼fh) = some (cancel-epi fg∼fh)
    where instance _ = P
  isEpi.cancel-epi (preserve-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 P) {z} {zero} {zero} fg∼fh = refl


instance
  hasFree:𝐂𝐚𝐭,𝐙𝐌𝐂𝐚𝐭 : hasFree (Category 𝑖) (𝐙𝐌𝐂𝐚𝐭 _)
  hasFree:𝐂𝐚𝐭,𝐙𝐌𝐂𝐚𝐭 = record { 𝑓𝑟𝑒𝑒ᵘ = λ 𝒞 -> ′ Free-𝐙𝐌𝐂𝐚𝐭 𝒞 ′ }

module _ {𝒞 : Category 𝑖} {{SP : isSizedCategory 𝒞}} where
  -- private
  --   sizeC' : ∀{a b : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} -> (p : HomPair a b) -> ⟨ SizeC ⟩
  --   sizeC' (some x , g) = {!!}
  --   sizeC' (zero , some x) = {!!}
  --   sizeC' (zero , zero) = ⊥-WFT

  instance
    isSizedCategory:Free-𝐙𝐌𝐂𝐚𝐭 : isSizedCategory ′(Free-𝐙𝐌𝐂𝐚𝐭 𝒞)′
    isSizedCategory.SizeO isSizedCategory:Free-𝐙𝐌𝐂𝐚𝐭 = SizeO {{SP}}
    isSizedCategory.sizeO isSizedCategory:Free-𝐙𝐌𝐂𝐚𝐭 = λ (incl x) → sizeO x

module _ {𝒞 : Category 𝑖} where
  instance
    isContradiction:zero≣some : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isContradiction (StrId {A = Hom-Free-𝐙𝐌𝐂𝐚𝐭 (incl a) (incl b)} (zero) (some f))
    isContradiction:zero≣some = contradiction (λ ())

    isContradiction:zero∼some : ∀{a b : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> isContradiction (_∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭_ {a = incl a} {b = incl b}  (zero) (some f))
    isContradiction:zero∼some = contradiction (λ ())

  cancel-injective-some-Free-𝐙𝐌𝐂𝐚𝐭 : ∀{a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> _∼-Hom-Free-𝐙𝐌𝐂𝐚𝐭_ {a = incl a} {b = incl b} (some f) (some g) -> f ∼ g
  cancel-injective-some-Free-𝐙𝐌𝐂𝐚𝐭 (some x) = x


-- //

