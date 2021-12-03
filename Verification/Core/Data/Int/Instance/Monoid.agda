
module Verification.Core.Data.Int.Instance.Monoid where

open import Verification.Core.Conventions hiding (ℕ)

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
-- open import Verification.Core.Algebra.Ring
-- open import Verification.Core.Order.Linearorder
-- open import Verification.Core.Order.Preorder
-- open import Verification.Core.Order.Totalorder
-- open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.Int.Definition

instance
  isMonoid:ℤ : isMonoid ℤ
  isMonoid._⋆_ isMonoid:ℤ = _+-ℤ_
  isMonoid.◌ isMonoid:ℤ = pos 0
  isMonoid.unit-l-⋆ isMonoid:ℤ = (pos0+ _ ⁻¹)
  isMonoid.unit-r-⋆ isMonoid:ℤ = refl
  isMonoid.assoc-l-⋆ isMonoid:ℤ {a} {b} {c} = (assoc-+-ℤ a b c ⁻¹)
  -- isMonoid.assoc-r-⋆ isMonoid:ℤ {a} {b} {c} = (assoc-+-ℤ a b c)
  isMonoid._≀⋆≀_ isMonoid:ℤ (p) (q) = {!!} -- incl $ λ i -> p i +-ℤ q i

  isCommutative:ℤ : isCommutative ℤ
  isCommutative.comm-⋆ isCommutative:ℤ {a} {b} = comm-+-ℤ a b

instance
  isGroup:ℤ : isGroup ℤ
  isGroup.◡_ isGroup:ℤ a = _-ℤ_ 0 a
  isGroup.inv-l-⋆ isGroup:ℤ {a} = minusPlus a (pos 0)
  isGroup.inv-r-⋆ isGroup:ℤ {a} = comm-⋆ {a = a} ∙ (minusPlus a (pos 0))
  isGroup.cong-◡_ isGroup:ℤ (p) = {!!} -- incl $ λ i -> pos 0 -ℤ p i
