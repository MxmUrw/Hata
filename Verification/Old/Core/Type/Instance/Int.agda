
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Type.Instance.Int where

open import Verification.Conventions
open import Verification.Old.Core.Algebra.Basic.Abelian
open import Verification.Old.Core.Algebra.Basic.Monoid
open import Verification.Old.Core.Algebra.Basic.Group
open import Verification.Old.Core.Algebra.Basic.Ring
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Homotopy.Level
open import Verification.Old.Core.Type.Decidable

open import Cubical.Data.Bool renaming (_⊕_ to _⊕-Bool_)

fromSign : Bool -> ℕ -> ℤ
fromSign false zero = pos 0
fromSign false (suc n) = negsuc n
fromSign true n = pos n

_⋅-ℤ_ : ℤ -> ℤ -> ℤ
a ⋅-ℤ b = fromSign (sgn a ⊕-Bool sgn b) (abs a *-ℕ abs b)


instance
  IDiscrete:ℤ : IDiscrete ℤ
  IDec.decide (IDiscrete.Impl IDiscrete:ℤ) = discreteInt _ _

instance
  ISet:ℤ : ISet ℤ
  IHType.hlevel ISet:ℤ = isSetInt

instance
  IAbelian:ℤ : IAbelian ℤ
  IMonoid.𝟷 (IAbelian.AsMult IAbelian:ℤ) = pos 0
  IMonoid._⋅_ (IAbelian.AsMult IAbelian:ℤ) = _+-ℤ_
  IMonoid.assoc-⋅ (IAbelian.AsMult IAbelian:ℤ) = {!!}
  IMonoid.unit-l-⋅ (IAbelian.AsMult IAbelian:ℤ) = {!!}
  IMonoid.unit-r-⋅ (IAbelian.AsMult IAbelian:ℤ) = {!!}
  IAbelian.AsMultInv IAbelian:ℤ IMonoid:WithInverse.⁻¹-Monoid =  λ a -> 0 -ℤ a
  -- IMonoid.𝟷 (IAbelian.AsMult IAbelian:ℤ) = pos 0
  -- IMonoid._⋅_ (IAbelian.AsMult IAbelian:ℤ) = _+-ℤ_
  -- IAbelian.AsMultInv IAbelian:ℤ IMonoid:WithInverse.⁻¹-Monoid =
  -- IAbelian.asGroup IAbelian:ℤ = {!!}
  -- IAbelian.𝟶 IAbelian:ℤ = pos 0
  -- IAbelian.- IAbelian:ℤ = λ a -> 0 -ℤ a
  -- IAbelian._+_ IAbelian:ℤ = _+-ℤ_

instance
  IMonoid:ℤ : IMonoid ℤ
  IMonoid.𝟷 IMonoid:ℤ = pos 1
  IMonoid._⋅_ IMonoid:ℤ = _⋅-ℤ_
  IMonoid.assoc-⋅ IMonoid:ℤ = {!!}
  IMonoid.unit-l-⋅ IMonoid:ℤ = {!!}
  IMonoid.unit-r-⋅ IMonoid:ℤ = {!!}

Ring:ℤ : Ring ℓ₀
⟨ Ring:ℤ ⟩ = ℤ
IRing.Multiplicative (of Ring:ℤ) = IMonoid:ℤ
IRing.Additive (of Ring:ℤ) = IAbelian:ℤ

instance IRing:ℤ = #openstruct Ring:ℤ
  -- IMonoid.𝟷 IMonoid:ℤ = pos 1
  -- IMonoid._⋅_ IMonoid:ℤ = _⋅-ℤ_


