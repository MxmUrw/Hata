
module Verification.Explorational.Theory.Std.Generic.Path.Definition where

open import Verification.Conventions hiding (_⊕_)
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition

record PathsAxiom (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  field Con₀ : 𝒰 𝑖
  field Con₁ : 𝒰 𝑖

open PathsAxiom public

module _ {𝑨 : PathsAxiom 𝑖} where
  data Paths (B : 𝒰 𝑖) : 𝒰 𝑖 where
    _0-⧜_ : Paths B
    _1-⧜_ : Paths B
    _+-⧜_ : (x y : Paths B) -> Paths B
    incl₀ : Con₀ 𝑨 -> Paths B
    incl₁ : Con₁ 𝑨 -> Paths B -> Paths B
    _⋅-⧜_ : (x y : Paths B) -> Paths B

  data ♮Paths (B : 𝒰 𝑖) : 𝒰 𝑖 where

  -- _⊕_ : ∀{A B : 𝒰 𝑖} -> Paths A -> Paths B -> Paths (A + B)
  -- _⊕_ t s = {!!}






