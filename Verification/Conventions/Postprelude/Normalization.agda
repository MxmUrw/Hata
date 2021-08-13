
module Verification.Conventions.Postprelude.Normalization where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta2.Macros
open import Verification.Conventions.Meta.Universe
-- open import Verification.Conventions.Prelude.Data.StrictId


record hasNormalization (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor normalization
  field ♮ᵘ : A -> B

open hasNormalization {{...}} public

macro
  ♮ : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : hasNormalization A B}} -> SomeStructure
  ♮ = #structureOn ♮ᵘ


