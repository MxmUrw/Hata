
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

module _ {𝒞' : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞'}} where
  private
    macro 𝒞 = #structureOn ⟨ 𝒞' ⟩
    instance
      _ : isSetoid 𝒞
      _ = isSetoid:byCategory

  unit-l-⊔ : ∀{a : 𝒞} -> ⊥ ⊔ a ∼ a
  unit-l-⊔ = {!!}

  unit-r-⊔ : ∀{a : 𝒞} -> a ⊔ ⊥ ∼ a
  unit-r-⊔ = {!!}

  assoc-l-⊔ : ∀{a b c : 𝒞} -> a ⊔ b ⊔ c ∼ a ⊔ (b ⊔ c)
  assoc-l-⊔ = {!!}

  isMonoid:byCoproduct : isMonoid 𝒞
  isMonoid:byCoproduct = record
                           { _⋆_ = _⊔_
                           ; ◌ = ⊥
                           ; unit-l-⋆ = {!!}
                           ; unit-r-⋆ = {!!}
                           ; assoc-l-⋆ = {!!}
                           ; _≀⋆≀_ = {!!}
                           }

