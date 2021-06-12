
module Verification.Experimental.Algebra.MonoidWithZero.Ideal.Lattice where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Ideal


module _ {M : Monoid₀ 𝑖} where
  Leading-r : Ideal-r M -> ⟨ M ⟩ -> Prop _
  Leading-r I = λ i → ∣ (∀ x -> (∑ λ a -> x ∼ i ⋆ a) -> ⟨ ⟨ I ⟩ x ⟩) ∣

  module Leading-r:1 where
    lem-10 : ∀{I J : Ideal-r M} -> (I ≤ J) -> Leading-r I ≤ Leading-r J
    lem-10 {I} {J} I≤J = incl (λ {a} LIa -> λ x (a , x∼ia) →
                            let P₁ : ⟨ ⟨ I ⟩ x ⟩
                                P₁ = LIa x (a , x∼ia)
                            in ⟨ I≤J ⟩ P₁
                            )






