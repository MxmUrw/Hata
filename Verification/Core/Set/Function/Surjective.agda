
module Verification.Core.Set.Function.Surjective where

open import Verification.Conventions

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  record isSurjective-𝒰 (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
    constructor surjective
    field surj-𝒰 : B -> A
    field inv-surj-𝒰 : ∀{b : B} -> f (surj-𝒰 b) ≡ b

  open isSurjective-𝒰 {{...}} public

