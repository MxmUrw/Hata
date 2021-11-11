
module Verification.Core.Data.Rational.Inclusion where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Rational.Definition
open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid
open import Verification.Core.Algebra.Group
open import Verification.Core.Algebra.Ring
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Ring.Localization
open import Verification.Core.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Core.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Core.Algebra.Field.Definition
open import Verification.Core.Order.Linearorder
open import Verification.Core.Order.Preorder

open AbelianMonoidNotation

data not-zero : ℕ -> 𝒰₀ where
  instance incl : ∀{n} -> not-zero (suc n)

instance
  hasInclusion:ℕ,ℚ : hasInclusion ℕ ℚ
  hasInclusion:ℕ,ℚ = inclusion (λ n -> let n' : ℤ
                                           n' = ι n
                                       in ι n')

module _ {a : ℕ} where
  private
    a' : ℚ
    a' = ι a
  instance
    not-◌:ι-ℕ : {{not-zero a}} -> not-◌ a'
    not-◌:ι-ℕ = {!!}



