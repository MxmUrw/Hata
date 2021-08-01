
module Verification.Experimental.Data.Family.Instance.Monoid where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Data.Family.Definition

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Category.Std.Fibration.Definition
open import Verification.Experimental.Algebra.Monoid.Definition



module _ {𝒞 : Category 𝑖} where
  instance
    isSetoid:𝐅𝐚𝐦 : isSetoid (𝐅𝐚𝐦 𝒞 𝑗)
    isSetoid:𝐅𝐚𝐦 = isSetoid:byCategory

  private instance
    _ : isSetoid ⟨ 𝒞 ⟩
    _ = isSetoid:byCategory

  module _ {{_ : isMonoid ′ ⟨ 𝒞 ⟩ ′}} where


    _⋆-𝐅𝐚𝐦_ : Family 𝒞 𝑗 → Family 𝒞 𝑗 → Family 𝒞 𝑗
    _⋆-𝐅𝐚𝐦_ A B = {!!} since {!!}


    instance
      isMonoid:𝐅𝐚𝐦 : isMonoid (𝐅𝐚𝐦 𝒞 𝑗)
      isMonoid:𝐅𝐚𝐦 = record
                       { _⋆_        = _⋆-𝐅𝐚𝐦_
                       ; ◌          = {!!}
                       ; unit-l-⋆   = {!!}
                       ; unit-r-⋆   = {!!}
                       ; assoc-l-⋆  = {!!}
                       ; _`cong-⋆`_ = {!!}
                       }




