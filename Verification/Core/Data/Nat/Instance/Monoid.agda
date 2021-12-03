
module Verification.Core.Data.Nat.Instance.Monoid where

open import Verification.Core.Conventions renaming (ℕ to Nat)

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid
-- open import Verification.Core.Algebra.Group
-- open import Verification.Core.Algebra.Ring
-- open import Verification.Core.Order.Preorder
-- open import Verification.Core.Order.Totalorder

open import Verification.Core.Data.Nat.Definition


instance
  isMonoid:ℕ : isMonoid ℕ
  isMonoid:ℕ = record
                 { _⋆_ = _+-ℕ_
                 ; ◌ = 0
                 ; unit-l-⋆ = refl
                 ; unit-r-⋆ = {!!}
                 ; assoc-l-⋆ = {!!}
                 -- ; assoc-r-⋆ = {!!}
                 ; _≀⋆≀_ = {!!}
                 }

instance
  isCommutative:ℕ : isCommutative ℕ
  isCommutative:ℕ = {!!}


