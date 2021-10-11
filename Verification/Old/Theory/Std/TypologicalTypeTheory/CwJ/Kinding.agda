
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding where

open import Verification.Conventions

record isKinding (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field ∂ₖ : A -> A
  field {{isDiscrete:this}} : isDiscrete A

open isKinding {{...}} public

Kinding : ∀ (𝑖 : 𝔏) -> _
Kinding 𝑖 = _ :& isKinding {𝑖}




