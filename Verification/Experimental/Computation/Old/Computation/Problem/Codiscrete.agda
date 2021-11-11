
module Verification.Core.Theory.Computation.Problem.Codiscrete where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Computation.Problem.Definition

coDisc : 𝐏𝐫𝐨𝐛 𝑖 -> 𝐏𝐫𝐨𝐛 𝑖
coDisc Π = ′ ⟨ Π ⟩ ′ {{problem λ x → ⊥-𝒰}}

instance
  isFunctor:coDisc : isFunctor (𝐏𝐫𝐨𝐛 𝑖) (𝐏𝐫𝐨𝐛 𝑖) coDisc
  isFunctor:coDisc = {!!}


ε-coDisc : ∀{A : 𝐏𝐫𝐨𝐛 𝑖} -> coDisc A ⟶ A
ε-coDisc =
  let p = incl (λ ())
  in incl (′ id-𝒰 ′ {{record {deduct = p}}})

