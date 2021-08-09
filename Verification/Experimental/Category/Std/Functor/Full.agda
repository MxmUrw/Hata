
module Verification.Experimental.Category.Std.Functor.Full where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Set.Setoid.Morphism



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isFull (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field {{isSurjective:map}} : ∀{a b : ⟨ 𝒞 ⟩} -> isSurjective (map {{of F}} {a} {b})

  open isFull {{...}} public






