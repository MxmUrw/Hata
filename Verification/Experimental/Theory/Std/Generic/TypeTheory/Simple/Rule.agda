
module Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Rule where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Context
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement


record Rule-⦿ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _⊩_
  field fst : Ctx-⦿ (Jdg-⦿ A)
  field snd : Jdg-⦿ A
open Rule-⦿

infix 28 _⊩_


module _ (A : 𝒰 𝑖) where
  macro 𝖱-⦿ = #structureOn (Rule-⦿ A)

private
  module _ {A : 𝒰 𝑖} where
    _↷-Rule-⦿_ : (𝖢-⦿ A) -> (𝖱-⦿ A) -> (𝖱-⦿ A)
    _↷-Rule-⦿_ Γ (𝔧s ⊩ 𝔦)= map-Ctx-⦿ (Γ ↷_) 𝔧s ⊩ (Γ ↷ 𝔦)
    -- Γ (Δ ⊢ α) = (Γ ⋆ Δ ⊢ α)



module _ {A : 𝒰 𝑖} where
  instance
    isSetoid:Rule-⦿ : isSetoid (𝖱-⦿ A)
    isSetoid:Rule-⦿ = isSetoid:byPath

    hasAction-l:Rule-⦿ : hasAction-l (𝖢-⦿ A) (𝖱-⦿ A)
    hasAction-l:Rule-⦿ = record
      { _↷_ = _↷-Rule-⦿_
      ; assoc-l-↷ = {!!}
      ; _≀↷≀_ = {!!}
      }

