
module Verification.Core.Theory.TypeField.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Theory.Presentation.Signature.SingleSorted.Definition

record isDirSet (X : Setoid 𝑖) : 𝒰 (𝑖 ⁺) where
  field Dir : 𝒰₀
open isDirSet public

DirSet : ∀ 𝑖 -> 𝒰 _
DirSet 𝑖 = Setoid 𝑖 :& isDirSet

-- record DirSet 𝑖 : 𝒰 𝑖 where
--   ⟨_⟩ : Setoid 𝑖
--   Dir : 𝒰₀
-- open DirSet public

record T∞ (X : DirSet 𝑖) (σ : 𝒰₀) : 𝒰 (𝑖 ⁺) where
  inductive
  -- field map0 : ⟨ X ⟩ -> (Bool) +-𝒰 ((∑ Var σ) ×-𝒰 (Dir (of X) -> T∞ X σ))



