
module Verification.Core.Computation.Question.Construction.MonoidalProduct where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Computation.Question.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Computation.Question.Construction.Product


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
      ; _≀⋆≀_ = {!!}
      }
    where _⋆'_ = λ 𝔓 𝔔 → (⟨ 𝔓 ⟩ ×-𝒰 ⟨ 𝔔 ⟩) since answerWith (λ (p , q) → p ‽ × q ‽)

_⊗_ = _⋆_
-- macro
--   _⊗_ : ∀{A : 𝒰 _} {{_ : Monoid 𝑖 on A}} -> A [ 𝑗 ]

