
module Verification.Experimental.Set.Function.Injective where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  record isInjective (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
    field injective : ∀ {a b} -> f a ≡-Str f b -> a ≡-Str b

  open isInjective {{...}} public






