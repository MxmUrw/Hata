
module Verification.Experimental.Set.Function.Injective where

open import Verification.Conventions


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  record isInjective (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
    constructor injective
    field cancel-injective : ∀ {a b} -> f a ≡ f b -> a ≡ b

  open isInjective {{...}} public







