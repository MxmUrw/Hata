
module Verification.Experimental.Data.Universe.Instance.Lattice where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Instance.Setoid
open import Verification.Experimental.Data.Universe.Instance.Preorder

instance
  hasFiniteJoins:𝒰 : hasFiniteJoins ′ 𝒰 𝑖 ′
  hasFiniteJoins.⊥         hasFiniteJoins:𝒰 = ⊥-𝒰
  hasFiniteJoins.initial-⊥ hasFiniteJoins:𝒰 = incl $ λ {()}
  hasFiniteJoins._∨_       hasFiniteJoins:𝒰 = _+-𝒰_
  hasFiniteJoins.ι₀-∨      hasFiniteJoins:𝒰 = incl left
  hasFiniteJoins.ι₁-∨      hasFiniteJoins:𝒰 = incl right
  hasFiniteJoins.[_,_]-∨   hasFiniteJoins:𝒰 f g = incl $ either ⟨ f ⟩ ⟨ g ⟩

instance
  hasFiniteMeets:𝒰 : hasFiniteMeets ′ 𝒰 𝑖 ′
  hasFiniteMeets:𝒰 = record
    { ⊤ = ⊤-𝒰
    ; terminal-⊤ = incl (λ x → tt)
    ; _∧_ = _×-𝒰_
    ; π₀-∧ = incl fst
    ; π₁-∧ = incl snd
    ; ⟨_,_⟩-∧ = λ f g -> incl (λ x → (⟨ f ⟩ x , ⟨ g ⟩ x))
    }


