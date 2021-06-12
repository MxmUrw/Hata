
module Verification.Experimental.Data.Universe.Instance.Setoid where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition


record isIso-𝒰 {a : 𝒰 𝑖} {b : 𝒰 𝑗} (f : a -> b) : 𝒰 (𝑖 ､ 𝑗) where
  field inverse-𝒰 : b -> a
        inv-r-◆-𝒰 : f ◆-𝒰 inverse-𝒰 ≡ id-𝒰
        inv-l-◆-𝒰 : inverse-𝒰 ◆-𝒰 f ≡ id-𝒰
open isIso-𝒰 {{...}} public

_≅-𝒰_ : (A : 𝒰 𝑖) (B : 𝒰 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
A ≅-𝒰 B = (A -> B) :& isIso-𝒰

private
  lem-10 : ∀{A : 𝒰 𝑖} -> isIso-𝒰 (id-𝒰 {A = A})
  isIso-𝒰.inverse-𝒰 lem-10 = id-𝒰
  isIso-𝒰.inv-r-◆-𝒰 lem-10 = refl
  isIso-𝒰.inv-l-◆-𝒰 lem-10 = refl

  lem-20 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> {f : A ≅-𝒰 B} -> isIso-𝒰 inverse-𝒰
  isIso-𝒰.inverse-𝒰 (lem-20 {f = f}) = ⟨ f ⟩
  isIso-𝒰.inv-r-◆-𝒰 (lem-20 {f = f}) = inv-l-◆-𝒰
  isIso-𝒰.inv-l-◆-𝒰 (lem-20 {f = f}) = inv-r-◆-𝒰

  lem-30 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> {f : A ≅-𝒰 B} -> {g : B ≅-𝒰 C} -> isIso-𝒰 (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)
  isIso-𝒰.inverse-𝒰 (lem-30 {f = f}) = inverse-𝒰 ◆-𝒰 inverse-𝒰
  isIso-𝒰.inv-r-◆-𝒰 (lem-30 {f = f}) = {!!}
  isIso-𝒰.inv-l-◆-𝒰 (lem-30 {f = f}) = {!!}

instance
  isEquivRel:≅-𝒰 : isEquivRel (∼-Base (_≅-𝒰_ {𝑖} {𝑖}))
  isEquivRel.refl isEquivRel:≅-𝒰 = incl (′ id-𝒰 ′ {{lem-10}})
  isEquivRel.sym  isEquivRel:≅-𝒰 (incl f) = incl (′ inverse-𝒰 ′ {{lem-20 {f = f}}})
  isEquivRel._∙_  isEquivRel:≅-𝒰 (incl f) (incl g) = incl (′ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩ ′ {{lem-30 {f = f} {g = g}}})

instance
  isSetoid:𝒰 : isSetoid _ (𝒰 𝑖)
  isSetoid._∼'_ isSetoid:𝒰 A B = A ≅-𝒰 B




