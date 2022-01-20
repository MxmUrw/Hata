
module Verification.Core.Category.Std.Morphism.Iso.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full


-- [Definition]
-- | Let [..] [] be a category.
module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where

  -- | An arrow |f : a ⟶ b| in |𝒞| is called an /isomorphism/,
  -- | if the following data is given.
  record isIso {a b : 𝒞} (f : Hom' {𝒞 = ′ 𝒞 ′} a b) : 𝒰 (𝑖 ､ 𝑗) where
  -- | 1. An inverse map [..].
    field inverse-◆ : b ⟶ a
  -- | 2. Proofs that it really is a left and right sided inverse.
          inv-r-◆ : ⟨ f ⟩ ◆ inverse-◆ ∼ id
          inv-l-◆ : inverse-◆ ◆ ⟨ f ⟩ ∼ id
  open isIso public

  -- //

  -- [Hide]
  _≅_ : (a b : 𝒞) -> 𝒰 (𝑖 ､ 𝑗)
  A ≅ B = Hom' A B :& isIso

  instance
    isSetoid:≅ : ∀{a b : 𝒞} -> isSetoid (a ≅ b)
    isSetoid:≅ = isSetoid:∼-Base (isSetoid:byDef (λ p q -> ⟨ p ⟩ ∼ ⟨ q ⟩) refl sym _∙_)

  private
    lem-10 : ∀{A : 𝒞} -> isIso (hom (id {a = A}))
    isIso.inverse-◆ lem-10 = id
    isIso.inv-r-◆ lem-10 = unit-2-◆
    isIso.inv-l-◆ lem-10 = unit-2-◆

    lem-20 : ∀{A : 𝒞} {B : 𝒞} -> {f : A ≅ B} -> isIso (hom (inverse-◆ (of f)))
    isIso.inverse-◆ (lem-20 {f = f}) = ⟨ f ⟩
    isIso.inv-r-◆ (lem-20 {f = f}) = inv-l-◆ (of f)
    isIso.inv-l-◆ (lem-20 {f = f}) = inv-r-◆ (of f)

    lem-30 : ∀{A : 𝒞} {B : 𝒞} {C : 𝒞} -> {f : A ≅ B} -> {g : B ≅ C} -> isIso (hom (⟨ f ⟩ ◆ ⟨ g ⟩))
    isIso.inverse-◆ (lem-30 {f = f} {g}) = inverse-◆ (of g) ◆ inverse-◆ (of f)
    isIso.inv-r-◆ (lem-30 {f = f}) = {!!}
    isIso.inv-l-◆ (lem-30 {f = f}) = {!!}


  refl-≅ : ∀{A : 𝒞} -> A ≅ A
  refl-≅ = id since lem-10

  sym-≅ : ∀{A B : 𝒞} -> A ≅ B -> B ≅ A
  sym-≅ p = inverse-◆ (of p) since lem-20 {f = p}

  _∙-≅_ : ∀{A B C : 𝒞} -> A ≅ B -> B ≅ C -> A ≅ C
  _∙-≅_ p q = ⟨ p ⟩ ◆ ⟨ q ⟩ since lem-30 {f = p} {g = q}


  isSetoid:byCategory : isSetoid 𝒞
  isSetoid:byCategory = isSetoid:byDef _≅_ refl-≅ sym-≅ _∙-≅_

  ⟨_⟩⁻¹ : ∀{a b} -> a ≅ b -> b ⟶ a
  ⟨_⟩⁻¹ f = inverse-◆ (of f)


-- //

-- [Hide]
-- | Equation syntax for ≅

module _ {A : 𝒰 𝑖} {{_ : isCategory {𝑗} A}} where
  _⟨_⟩-≅_ : (x : A) {y : A} {z : A} → x ≅ y → y ≅ z → x ≅ z
  _ ⟨ x≡y ⟩-≅ y≡z = x≡y ∙-≅ y≡z

  ⟨⟩-≅-syntax : (x : A) {y z : A} → x ≅ y → y ≅ z → x ≅ z
  ⟨⟩-≅-syntax = _⟨_⟩-≅_
  infixr 2 ⟨⟩-≅-syntax
  infixr 2 _⟨_⟩-≅_

  infix  3 _∎-≅

  _∎-≅ : (x : A) → x ≅ x
  _ ∎-≅ = refl-≅

-- //

