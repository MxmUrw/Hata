
module Verification.Experimental.Category.Std.Functor.Image where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Set.Setoid.Morphism


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  module _ (F : Functor 𝒞 𝒟) where

    inEssentialImage : ⟨ 𝒟 ⟩ -> 𝒰 _
    inEssentialImage d = ∑ λ (c : ⟨ 𝒞 ⟩) -> ⟨ F ⟩ c ≅ d

    EssentialImage : 𝒰 _
    EssentialImage = ∑ inEssentialImage


