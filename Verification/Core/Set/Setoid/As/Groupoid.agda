
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


