
module Verification.Experimental.Set.Set.Instance.Category where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Category.Std.Category.Definition

instance
  isCategory:Set : isCategory _ (𝐒𝐞𝐭 𝑖)
  isCategory.Hom' isCategory:Set = λ A B -> ⟨ A ⟩ -> ⟨ B ⟩
  isCategory.isSetoid:Hom isCategory:Set = {!!}
  isCategory.id isCategory:Set = {!!}
  isCategory._◆_ isCategory:Set = {!!}
  isCategory.unit-l-◆ isCategory:Set = {!!}
  isCategory.unit-r-◆ isCategory:Set = {!!}
  isCategory.unit-2-◆ isCategory:Set = {!!}
  isCategory.assoc-l-◆ isCategory:Set = {!!}
  isCategory.assoc-r-◆ isCategory:Set = {!!}
  isCategory._◈_ isCategory:Set = {!!}




