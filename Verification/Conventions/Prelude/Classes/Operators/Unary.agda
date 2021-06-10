

module Verification.Conventions.Prelude.Classes.Operators.Unary where

open import Verification.Conventions.Proprelude

record Notation-Absolute (A : 𝒰 𝑖) (B : 𝒰 𝑗) : (𝒰 (𝑖 ⊔ 𝑗)) where
  field ∣_∣ : A -> B
  infix 50 ∣_∣

open Notation-Absolute {{...}} public

record Notation-Inverse (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  field _⁻¹ : A -> B
  infix 300 _⁻¹
open Notation-Inverse {{...}} public

--------------------------------------------------------------------
-- ====* Join notation

record IMultiJoinable (X : 𝒰 𝑖) (V : 𝒰 𝑗) : 𝒰 (𝑗 ⊔ 𝑖 ⁺) where
  field ⨆ : X -> V

open IMultiJoinable {{...}} public




