
module Verification.Experimental.Theory.TypeField.Substitution.Simple where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Sum.Definition


module _ {𝕋 𝕍 : 𝒰₀} where

  record TField : 𝒰₀ where
    field ⟨_⟩ : 𝕋 -> 𝕍

  open TField public





