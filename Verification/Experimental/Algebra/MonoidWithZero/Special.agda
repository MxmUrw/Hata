
module Verification.Experimental.Algebra.MonoidWithZero.Special where

open import Verification.Conventions

open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition


record hasSpecial (M : 𝐌𝐨𝐧₀ 𝑖) : 𝒰 (𝑖 ⁺) where
  field Special : Submonoid ′ ⟨ M ⟩ ′

open hasSpecial {{...}} public




