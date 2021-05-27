
module Verification.Experimental.Data.Prop.Instance.HeytingAlgebra where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.HeytingAlgebra
open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Data.Prop.Instance.Setoid
open import Verification.Experimental.Data.Prop.Instance.Preorder
open import Verification.Experimental.Data.Prop.Instance.Lattice
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Instance.Preorder
open import Verification.Experimental.Data.Universe.Instance.Lattice
open import Verification.Experimental.Data.Sum.Definition

instance
  isHeytingAlgebra:Prop : isHeytingAlgebra ′ Prop 𝑖 ′
  isHeytingAlgebra._⇒_     isHeytingAlgebra:Prop A B = ∣ (⟨ A ⟩ -> ⟨ B ⟩) ∣
  isHeytingAlgebra.embed-⇒ isHeytingAlgebra:Prop = incl (λ a b -> a , b)
  isHeytingAlgebra.eval-⇒  isHeytingAlgebra:Prop = incl (λ (a , f) -> f a)
