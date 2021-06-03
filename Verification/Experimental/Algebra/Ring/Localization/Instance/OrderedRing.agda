
module Verification.Experimental.Algebra.Ring.Localization.Instance.OrderedRing where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Localization
open import Verification.Experimental.Algebra.Ring.Ordered
open import Verification.Experimental.Algebra.Ring.Domain

open import Verification.Experimental.Order.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Ring


module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} {R : CRing 𝑖} {M : MCS R}
         {{_ : isOrderedRing 𝑗 ′ ⟨ R ⟩ ′}}
         {{_ : hasNotZero-MCS M}}
         {{δ : hasRepr (Localize R M) hasPositiveDenom}} where


  instance
    isOrderedRing:Localize : isOrderedRing _ ′(Localize R M)′
    isOrderedRing:Localize = record { stronglyMonotone-l-⋆ = lem-10 ; preservesPositivity-⋅ = {!!} }
      where
        lem-10 : ∀{a b} -> a < b -> ∀{c} -> a ⋆ c < b ⋆ c
        lem-10 = {!!}


