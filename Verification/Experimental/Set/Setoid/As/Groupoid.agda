
module Verification.Experimental.Set.Setoid.As.Groupoid where

open import Verification.Conventions
-- open import Verification.Experimental.Data.Prop.Definition
-- open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Codiscrete
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Groupoid.Definition
open import Verification.Experimental.Set.Setoid.As.Category
open import Verification.Experimental.Category.Std.Morphism.Iso


module _ {A : 𝒰 𝑖} {{Ap : isSetoid {𝑗} A}} where

  private instance
    _ : isCategory {_ , 𝑘} A
    _ = isCategory:bySetoid

  isGroupoid:bySetoid : isGroupoid {_ , _ , 𝑘} ′ A ′
  isGroupoid.isIso:hom isGroupoid:bySetoid {a} {b} {ϕ} = P
    where
      P : isIso (hom ϕ)
      P = record
          { inverse-◆ = sym ϕ
          ; inv-r-◆   = tt
          ; inv-l-◆   = tt
          }


