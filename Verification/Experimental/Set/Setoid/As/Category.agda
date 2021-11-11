
module Verification.Core.Set.Setoid.As.Category where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Definition
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Discrete
open import Verification.Core.Category.Std.Category.Definition


module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where

  isCategory:bySetoid : isCategory {_ , _} A
  isCategory.Hom isCategory:bySetoid          = λ a b -> a ∼ b
  isCategory.isSetoid:Hom isCategory:bySetoid = isSetoid:byDiscrete
  isCategory.id isCategory:bySetoid           = refl
  isCategory._◆_ isCategory:bySetoid          = _∙_
  isCategory.unit-l-◆ isCategory:bySetoid     = {!!}
  isCategory.unit-r-◆ isCategory:bySetoid     = {!!}
  isCategory.unit-2-◆ isCategory:bySetoid     = {!!}
  isCategory.assoc-l-◆ isCategory:bySetoid    = {!!}
  isCategory.assoc-r-◆ isCategory:bySetoid    = {!!}
  isCategory._◈_ isCategory:bySetoid          = λ x x₁ → {!!}


