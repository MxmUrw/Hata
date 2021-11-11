
module Verification.Core.Data.Prop.Instance.HeytingAlgebra where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.HeytingAlgebra
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Prop.Instance.Setoid
open import Verification.Core.Data.Prop.Instance.Preorder
open import Verification.Core.Data.Prop.Instance.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Preorder
open import Verification.Core.Data.Universe.Instance.Lattice
open import Verification.Core.Data.Sum.Definition

instance
  isHeytingAlgebra:Prop : isHeytingAlgebra ′ Prop 𝑖 ′
  isHeytingAlgebra._⇒_     isHeytingAlgebra:Prop A B = ∣ (⟨ A ⟩ -> ⟨ B ⟩) ∣
  isHeytingAlgebra.embed-⇒ isHeytingAlgebra:Prop = incl (λ a b -> a , b)
  isHeytingAlgebra.eval-⇒  isHeytingAlgebra:Prop = incl (λ (a , f) -> f a)
