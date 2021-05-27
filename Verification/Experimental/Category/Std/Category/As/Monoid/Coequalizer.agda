
module Verification.Experimental.Category.Std.Category.As.Monoid.Coequalizer where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer


module _ {𝒞 : Category 𝑖} where
  module _ (a b : ⟨ 𝒞 ⟩) (f g : a ⟶ b) where
    lem-10 : Unification f g -> isEpiPrincipal (MonCoequalizing f g)
    lem-10 = {!!}

    lem-20 : isEpiPrincipal (MonCoequalizing (arrow f) (arrow g)) -> Unification f g
    lem-20 = {!!}



