
module Verification.Experimental.Category.Std.Functor.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  instance
    isCategory:Functor : isCategory _ (Functor 𝒞 𝒟)
    isCategory.Hom isCategory:Functor = Hom-Base Natural
    isCategory.isSetoid:Hom isCategory:Functor = isSetoid:Natural
    isCategory.id isCategory:Functor = {!!}
    isCategory._◆_ isCategory:Functor = {!!}
    isCategory.unit-l-◆ isCategory:Functor = {!!}
    isCategory.unit-r-◆ isCategory:Functor = {!!}
    isCategory.unit-2-◆ isCategory:Functor = {!!}
    isCategory.assoc-l-◆ isCategory:Functor = {!!}
    isCategory.assoc-r-◆ isCategory:Functor = {!!}
    isCategory._◈_ isCategory:Functor = {!!}

module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  macro 𝐅𝐮𝐧𝐜 = #structureOn (Functor 𝒞 𝒟)


