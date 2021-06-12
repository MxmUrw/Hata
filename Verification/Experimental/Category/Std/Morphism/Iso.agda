
module Verification.Experimental.Category.Std.Morphism.Iso where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition

module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory 𝑖 𝒞}} where

  record isIso {a b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑗 ､ 𝑖) where
    field inverse-◆ : b ⟶ a
          inv-r-◆ : f ◆ inverse-◆ ∼ id
          inv-l-◆ : inverse-◆ ◆ f ∼ id
  open isIso public

  _≅_ : (a b : 𝒞) -> 𝒰 (𝑗 ､ 𝑖)
  A ≅ B = (A ⟶ B) :& isIso

  private
    lem-10 : ∀{A : 𝒞} -> isIso (id {a = A})
    isIso.inverse-◆ lem-10 = id
    isIso.inv-r-◆ lem-10 = unit-2-◆
    isIso.inv-l-◆ lem-10 = unit-2-◆

    lem-20 : ∀{A : 𝒞} {B : 𝒞} -> {f : A ≅ B} -> isIso (inverse-◆ (of f))
    isIso.inverse-◆ (lem-20 {f = f}) = ⟨ f ⟩
    isIso.inv-r-◆ (lem-20 {f = f}) = inv-l-◆ (of f)
    isIso.inv-l-◆ (lem-20 {f = f}) = inv-r-◆ (of f)

    lem-30 : ∀{A : 𝒞} {B : 𝒞} {C : 𝒞} -> {f : A ≅ B} -> {g : B ≅ C} -> isIso (⟨ f ⟩ ◆ ⟨ g ⟩)
    isIso.inverse-◆ (lem-30 {f = f} {g}) = inverse-◆ (of g) ◆ inverse-◆ (of f)
    isIso.inv-r-◆ (lem-30 {f = f}) = {!!}
    isIso.inv-l-◆ (lem-30 {f = f}) = {!!}

  iso-inv : ∀{A B : 𝒞} -> A ≅ B -> B ≅ A
  ⟨ iso-inv ϕ ⟩ = inverse-◆ (of ϕ)
  _:&_.oldProof (iso-inv ϕ) = record {}
  _:&_.of iso-inv ϕ = lem-20 {f = ϕ}

  instance
    isEquivRel:≅ : isEquivRel (∼-Base (_≅_))
    isEquivRel.refl isEquivRel:≅ = incl (′ id ′ {{lem-10}})
    isEquivRel.sym  isEquivRel:≅ (incl f) = incl (′ inverse-◆ (of f) ′ {{lem-20 {f = f}}})
    isEquivRel._∙_  isEquivRel:≅ (incl f) (incl g) = incl (′ ⟨ f ⟩ ◆ ⟨ g ⟩ ′ {{lem-30 {f = f} {g = g}}})

  isSetoid:Category : isSetoid _ 𝒞
  isSetoid._∼'_ isSetoid:Category A B = A ≅ B

