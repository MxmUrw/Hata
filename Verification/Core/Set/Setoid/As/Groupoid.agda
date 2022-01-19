
module Verification.Core.Set.Setoid.As.Groupoid where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Definition
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Codiscrete
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Groupoid.Definition
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Category.Std.Morphism.Iso

-- NOTE:
-- This concept does not make much sense.
-- A setoid has as much information as a category,
-- but does not follow the laws of categories.
-- Thus it is not possible to embed it in the structure
-- of a category, without building a quotient for
-- the equality of arrows.


{-
module _ {A : 𝒰 𝑖} {{Ap : isSetoid {𝑗} A}} where

  private instance
    _ : isCategory {_ , _} A
    _ = isCategory:bySetoid

  isGroupoid:bySetoid : isGroupoid {_ , _ , _} ′ A ′
  isGroupoid.isIso:hom isGroupoid:bySetoid {a} {b} {ϕ} = P
    where
      P : isIso (hom ϕ)
      P = record
          { inverse-◆ = sym ϕ
          ; inv-r-◆   = {!!}
          ; inv-l-◆   = {!!}
          }
-}

