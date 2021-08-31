
module Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Reflection where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

-- open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition

open import Verification.Experimental.Category.Std.Functor.Faithful
open import Verification.Experimental.Category.Std.Functor.Full
open import Verification.Experimental.Category.Std.Functor.EssentiallySurjective
open import Verification.Experimental.Set.Setoid.Morphism


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {F : Functor 𝒞 𝒟} {{_ : isFull F}} {{_ : isFaithful F}} where

  module _ {a b x : ⟨ 𝒞 ⟩} {f g : a ⟶ b} (P : isCoequalizer (map f) (map g) (⟨ F ⟩ x)) where
    private
      instance _ = P
      π₌' : b ⟶ x
      π₌' = surj π₌

    isCoequalizer:byFullyFaithfull : isCoequalizer f g x
    isCoequalizer.π₌ isCoequalizer:byFullyFaithfull = π₌'
    isCoequalizer.equate-π₌ isCoequalizer:byFullyFaithfull = {!!}
    isCoequalizer.compute-Coeq isCoequalizer:byFullyFaithfull = {!!}
    isCoequalizer.isEpi:π₌ isCoequalizer:byFullyFaithfull = {!!}

