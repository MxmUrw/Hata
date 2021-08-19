
module Verification.Experimental.Category.Std.Category.Opposite.Instance.Monoid where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso


module _ {𝒞 : Category 𝑖} where
  private instance
    _ : isSetoid ⟨ 𝒞 ⟩
    _ = isSetoid:byCategory

    _ : isSetoid (𝒞 ᵒᵖ⌯)
    _ = isSetoid:byCategory

  module _ {{_ : isMonoid ′ ⟨ 𝒞 ⟩ ′}} where

    instance
      isMonoid:ᵒᵖ : isMonoid (𝒞 ᵒᵖ⌯)
      isMonoid:ᵒᵖ = record
                      { _⋆_ = λ a b -> incl (⟨ a ⟩ ⋆ ⟨ b ⟩)
                      ; ◌ = incl ◌
                      ; unit-l-⋆ = {!!}
                      ; unit-r-⋆ = {!!}
                      ; assoc-l-⋆ = {!!}
                      ; _`cong-⋆`_ = {!!}
                      }



