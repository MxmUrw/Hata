
module Verification.Core.Data.Family.Instance.Monoid where

open import Verification.Core.Conventions
open import Verification.Core.Data.Family.Definition

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Category.Std.Fibration.Definition
open import Verification.Core.Algebra.Monoid.Definition



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




