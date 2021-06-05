
module Verification.Experimental.Computation.Question.Construction.MonoidalProduct where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Computation.Question.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Computation.Question.Construction.Product


instance
  isSetoid:Question : isSetoid _ (𝐐𝐮𝐞𝐬𝐭 𝑖)
  isSetoid:Question = isSetoid:Category

instance
  isMonoid:Question : isMonoid (𝐐𝐮𝐞𝐬𝐭 𝑖)
  isMonoid:Question = record
      { _⋆_ = _⋆'_
      ; ◌ = {!!}
      ; unit-l-⋆ = {!!}
      ; unit-r-⋆ = {!!}
      ; assoc-l-⋆ = {!!}
      ; assoc-r-⋆ = {!!}
      ; _`cong-⋆`_ = {!!}
      }
    where _⋆'_ = λ 𝔓 𝔔 → (⟨ 𝔓 ⟩ ×-𝒰 ⟨ 𝔔 ⟩) since answerWith (λ (p , q) → p ‽ × q ‽)

_⊗_ = _⋆_
-- macro
--   _⊗_ : ∀{A : 𝒰 _} {{_ : Monoid 𝑖 on A}} -> A [ 𝑗 ]

