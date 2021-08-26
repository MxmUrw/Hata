
module Verification.Experimental.Data.Nat.Free where

open import Verification.Experimental.Conventions renaming (ℕ to Nat)

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid
open import Verification.Experimental.Algebra.Monoid.Free.Definition


人ℕᵘ : 𝒰₀
人ℕᵘ = Free-𝐌𝐨𝐧 ⊤-𝒰

macro 人ℕ = #structureOn 人ℕᵘ

ι-人ℕ : Nat -> 人ℕ
ι-人ℕ zero = ◌
ι-人ℕ (suc n) = incl tt ⋆ ι-人ℕ n

instance
  fromNat人ℕ : HasFromNat 人ℕ
  fromNat人ℕ = record { Constraint = λ _ → 𝟙-𝒰 ; fromNat = λ n -> ι-人ℕ n }

人List = Free-𝐌𝐨𝐧

module _ {A : 𝒰 𝑖} where
  [_]ᶠ : Free-𝐌𝐨𝐧 A -> 𝒰 𝑖
  [_]ᶠ as = ∑ λ a -> as ∍ a

  leftᶠ : ∀{as bs} -> [ as ]ᶠ -> [ as ⋆ bs ]ᶠ
  leftᶠ (a , p) = a , left-∍ p

  rightᶠ : ∀{as bs} -> [ bs ]ᶠ -> [ as ⋆ bs ]ᶠ
  rightᶠ (a , p) = a , right-∍ p



