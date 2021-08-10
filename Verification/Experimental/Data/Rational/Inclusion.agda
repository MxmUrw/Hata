
module Verification.Experimental.Data.Rational.Inclusion where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Int.Definition
open import Verification.Experimental.Data.Rational.Definition
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Group
open import Verification.Experimental.Algebra.Ring
open import Verification.Experimental.Algebra.Ring.Ordered
open import Verification.Experimental.Algebra.Ring.Localization
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.OrderedRing
open import Verification.Experimental.Algebra.Field.Definition
open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Order.Preorder

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



