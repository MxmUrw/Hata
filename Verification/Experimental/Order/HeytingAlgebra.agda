
module Verification.Experimental.Order.HeytingAlgebra where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice


record isHeytingAlgebra {𝑖 : 𝔏 ^ 3} (L : Lattice 𝑖) : 𝒰 𝑖 where
  field _⇒_ : ⟨ L ⟩ -> ⟨ L ⟩ -> ⟨ L ⟩
  field embed-⇒ : ∀{a b : ⟨ L ⟩} -> a ≤ (b ⇒ (a ∧ b))
  field eval-⇒  : ∀{a b : ⟨ L ⟩} -> (a ∧ (a ⇒ b)) ≤ b

  ⫬_ : ⟨ L ⟩ -> ⟨ L ⟩
  ⫬_ a = a ⇒ ⊥

  _∖_ : ⟨ L ⟩ -> ⟨ L ⟩ -> ⟨ L ⟩
  a ∖ b = a ∧ ⫬ b

  infix 100 ⫬_
  infix 60 _∖_

open isHeytingAlgebra {{...}} public


module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}}
         {{_ : isLattice ′ A ′}} where
  instance
    isLattice:Family : ∀{I : 𝒰 𝑗} -> isLattice (′ (I -> A) ′)
    isLattice:Family = record {}


module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}}
         {{_ : isLattice ′ A ′}}
         {{_ : isHeytingAlgebra ′ A ′}} where
  instance
    isHeytingAlgebra:Family : ∀{I : 𝒰 𝑗} -> isHeytingAlgebra (′ (I -> A) ′)
    isHeytingAlgebra._⇒_     isHeytingAlgebra:Family = λ a b i -> a i ⇒ b i
    isHeytingAlgebra.embed-⇒ isHeytingAlgebra:Family = λ a -> embed-⇒
    isHeytingAlgebra.eval-⇒  isHeytingAlgebra:Family = λ a -> eval-⇒



