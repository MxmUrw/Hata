
module Verification.Core.Data.Nat.Definition where

open import Verification.Core.Conventions renaming (ℕ to Nat)

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete

ℕᵘ = Nat

macro
  ℕ : SomeStructure
  ℕ = #structureOn Nat

-- instance
--   isSetoid:ℕ : isSetoid _ ℕ
--   isSetoid._∼'_ isSetoid:ℕ = _≣_
--   isSetoid.isEquivRel:∼ isSetoid:ℕ = it



instance
  isDiscrete:ℕ : isDiscrete ℕ
  isDiscrete:ℕ = record { _≟-Str_ = discreteℕ }

instance
  isSet-Str:ℕ : isSet-Str ℕ
  isSet-Str:ℕ = {!!}









