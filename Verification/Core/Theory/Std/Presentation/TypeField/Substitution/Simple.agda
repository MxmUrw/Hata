
module Verification.Core.Theory.TypeField.Substitution.Simple where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Sum.Definition


module _ {𝕋 𝕍 : 𝒰₀} where

  record TField : 𝒰₀ where
    field ⟨_⟩ : 𝕋 -> 𝕍

  open TField public





