
module Verification.Core.Algebra.MonoidWithZero.Special where

open import Verification.Conventions

open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition


record hasSpecial (M : 𝐌𝐨𝐧₀ 𝑖) : 𝒰 (𝑖 ⁺) where
  field Special : Submonoid ′ ⟨ M ⟩ ′

open hasSpecial {{...}} public




