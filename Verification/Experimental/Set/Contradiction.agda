
module Verification.Experimental.Set.Contradiction where

open import Verification.Conventions

record isContradiction (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor contradiction
  field contradict : A -> ⊥-𝒰 {ℓ₀}

open isContradiction {{...}} public

module _ {A : 𝒰 𝑖} {{_ : isContradiction A}} where
  impossible : ∀{B : 𝒰 𝑗} -> A -> B
  impossible a with contradict a
  ... | ()

instance
  isContradiction:𝟘-𝒰 : isContradiction (𝟘-𝒰)
  isContradiction:𝟘-𝒰 = contradiction (𝟘-rec)

