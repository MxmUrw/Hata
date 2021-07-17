
module Verification.Experimental.Category.Std.Category.Instance.ProductMonoid where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Construction.Product


-- | Here we show that 𝐂𝐚𝐭, the category of categories is a monoid with respect to
--   the product.


◌-𝐂𝐚𝐭 : 𝐂𝐚𝐭 𝑖
◌-𝐂𝐚𝐭 = ′ Lift-Cat (𝟙 {ℓ₀}) ′

private
  infixl 40 _⊗_
  _⊗_ : 𝐂𝐚𝐭 𝑖 -> 𝐂𝐚𝐭 𝑖 -> 𝐂𝐚𝐭 𝑖
  _⊗_ 𝒞 𝒟 = 𝒞 × 𝒟

  lem-1 : {𝒞 : 𝐂𝐚𝐭 𝑖} -> ◌-𝐂𝐚𝐭 ⊗ 𝒞 ≅ 𝒞
  lem-1 = π₁-𝐂𝐚𝐭 since P
    where
      P = ?


instance
  isMonoid:𝐂𝐚𝐭 : isMonoid (𝐂𝐚𝐭 𝑖)
  isMonoid:𝐂𝐚𝐭 = record
                   { _⋆_         = _⊗_
                   ; ◌           = ◌-𝐂𝐚𝐭
                   ; unit-l-⋆    = lem-1
                   ; unit-r-⋆    = {!!}
                   ; assoc-l-⋆   = {!!}
                   ; assoc-r-⋆   = {!!}
                   ; _`cong-⋆`_  = {!!}
                   }





