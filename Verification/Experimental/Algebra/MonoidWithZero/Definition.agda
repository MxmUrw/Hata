
module Verification.Core.Algebra.MonoidWithZero.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition


record hasZero (A : Monoid 𝑖) : 𝒰 𝑖 where
  field ◍ : ⟨ A ⟩
  field absorb-r-⋆ : ∀{a : ⟨ A ⟩} -> a ⋆ ◍ ∼ ◍
  field absorb-l-⋆ : ∀{a : ⟨ A ⟩} -> ◍ ⋆ a ∼ ◍
  field decide-◍ : (a : ⟨ A ⟩) -> isDecidable (a ∼ ◍)
open hasZero {{...}} public

Monoid₀ : ∀ 𝑖 -> 𝒰 _
Monoid₀ 𝑖 = Monoid 𝑖 :& hasZero

module _ (𝑖) where
  macro 𝐌𝐨𝐧₀ = #structureOn (Monoid₀ 𝑖)

-- record zeroIsDecidable (A : Monoid₀ 𝑖) : 𝒰 𝑖 where
--   field decide-◍ : (a : ⟨ A ⟩) -> isDecidable (a ∼ ◍)
-- open zeroIsDecidable {{...}} public




