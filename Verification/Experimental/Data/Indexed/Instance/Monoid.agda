
module Verification.Experimental.Data.Indexed.Instance.Monoid where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition

open import Verification.Experimental.Algebra.Monoid.Definition


module _ {𝒞 : Category 𝑖} where
  private instance
    _ : isSetoid ⟨ 𝒞 ⟩
    _ = isSetoid:byCategory


  module _ {{_ : isMonoid ′ ⟨ 𝒞 ⟩ ′}} {I : 𝒰 𝑗} where

    _⋆-𝐈𝐱_ : Indexed I 𝒞 → Indexed I 𝒞 → Indexed I 𝒞
    _⋆-𝐈𝐱_ A B = indexed (λ i → ix A i ⋆ ix B i)

    ◌-𝐈𝐱 : Indexed I 𝒞
    ◌-𝐈𝐱 = indexed (const ◌)

    instance
      isMonoid:Indexed : isMonoid (𝐈𝐱 I 𝒞)
      isMonoid:Indexed = record
                           { _⋆_        = _⋆-𝐈𝐱_
                           ; ◌          = ◌-𝐈𝐱
                           ; unit-l-⋆   = {!!}
                           ; unit-r-⋆   = {!!}
                           ; assoc-l-⋆  = {!!}
                           ; _`cong-⋆`_ = {!!}
                           }




