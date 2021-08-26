
module Verification.Experimental.Category.Std.Category.Opposite.LiftFunctor where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Opposite.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  liftFunctor-ᵒᵖ⌯ : (F : Functor 𝒞 𝒟) -> Functor (𝒞 ᵒᵖ⌯) (𝒟 ᵒᵖ⌯)
  liftFunctor-ᵒᵖ⌯ F = {!!}



