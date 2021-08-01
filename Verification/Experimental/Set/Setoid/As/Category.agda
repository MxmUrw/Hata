
module Verification.Experimental.Set.Setoid.As.Category where

open import Verification.Conventions
-- open import Verification.Experimental.Data.Prop.Definition
-- open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Codiscrete
open import Verification.Experimental.Category.Std.Category.Definition


module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where

  isCategory:bySetoid : isCategory {_ , 𝑘} A
  isCategory.Hom isCategory:bySetoid          = λ a b -> a ∼ b
  isCategory.isSetoid:Hom isCategory:bySetoid = isSetoid:byCodiscrete
  isCategory.id isCategory:bySetoid           = refl
  isCategory._◆_ isCategory:bySetoid          = _∙_
  isCategory.unit-l-◆ isCategory:bySetoid     = tt
  isCategory.unit-r-◆ isCategory:bySetoid     = tt
  isCategory.unit-2-◆ isCategory:bySetoid     = tt
  isCategory.assoc-l-◆ isCategory:bySetoid    = tt
  isCategory.assoc-r-◆ isCategory:bySetoid    = tt
  isCategory._◈_ isCategory:bySetoid          = λ x x₁ → tt


