
module Verification.Experimental.Category.Std.Functor.Faithful where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Set.Setoid.Morphism



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isFaithful (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field {{isInjective:map}} : ∀{a b : ⟨ 𝒞 ⟩} -> isInjective (map {{of F}} {a} {b})

  open isFaithful {{...}} public







