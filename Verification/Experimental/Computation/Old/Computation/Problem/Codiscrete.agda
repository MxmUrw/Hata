
module Verification.Experimental.Theory.Computation.Problem.Codiscrete where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Computation.Problem.Definition

coDisc : 𝐏𝐫𝐨𝐛 𝑖 -> 𝐏𝐫𝐨𝐛 𝑖
coDisc Π = ′ ⟨ Π ⟩ ′ {{problem λ x → ⊥-𝒰}}

instance
  isFunctor:coDisc : isFunctor (𝐏𝐫𝐨𝐛 𝑖) (𝐏𝐫𝐨𝐛 𝑖) coDisc
  isFunctor:coDisc = {!!}


ε-coDisc : ∀{A : 𝐏𝐫𝐨𝐛 𝑖} -> coDisc A ⟶ A
ε-coDisc =
  let p = incl (λ ())
  in incl (′ id-𝒰 ′ {{record {deduct = p}}})

