
module Verification.Experimental.Algebra.MonoidWithZero.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition


record hasZero (A : Monoid 𝑖) : 𝒰 𝑖 where
  field ◍ : ⟨ A ⟩
  field absorb-r-⋆ : ∀{a : ⟨ A ⟩} -> a ⋆ ◍ ∼ ◍
  field absorb-l-⋆ : ∀{a : ⟨ A ⟩} -> ◍ ⋆ a ∼ ◍
open hasZero {{...}} public

Monoid₀ : ∀ 𝑖 -> 𝒰 _
Monoid₀ 𝑖 = Monoid 𝑖 :& hasZero

record zeroIsDecidable (A : Monoid₀ 𝑖) : 𝒰 𝑖 where
  field decide-◍ : (a : ⟨ A ⟩) -> isDecidable (a ∼ ◍)
open zeroIsDecidable {{...}} public




