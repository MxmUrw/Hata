
module Verification.Experimental.Category.Std.Morphism.Mono.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record isMono {a b : 𝒞} (ϕ : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor mono
    field cancel-mono : ∀{x : 𝒞} -> ∀{α β : x ⟶ a} -> α ◆ ϕ ∼ β ◆ ϕ -> α ∼ β

  open isMono {{...}} public






