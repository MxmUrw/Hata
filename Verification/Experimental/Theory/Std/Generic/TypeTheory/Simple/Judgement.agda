
module Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Context


record Jdg-⦿ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _⊢_
  field fst : Ctx-⦿ A
  field snd : A
open Jdg-⦿

infix 30 _⊢_

module _ (A : 𝒰 𝑖) where
  macro 𝖩-⦿ = #structureOn (Jdg-⦿ A)

private
  module _ {A : 𝒰 𝑖} where
    _↷-Jdg-⦿_ : (𝖢-⦿ A) -> (𝖩-⦿ A) -> (𝖩-⦿ A)
    _↷-Jdg-⦿_ Γ (Δ ⊢ α) = (Γ ⋆ Δ ⊢ α)



module _ {A : 𝒰 𝑖} where
  instance
    isSetoid:Jdg-⦿ : isSetoid (Jdg-⦿ A)
    isSetoid:Jdg-⦿ = isSetoid:byPath

    hasAction-l:Jdg-⦿ : hasAction-l (𝖢-⦿ A) (𝖩-⦿ A)
    hasAction-l:Jdg-⦿ = record
      { _↷_ = _↷-Jdg-⦿_
      ; assoc-l-↷ = {!!}
      ; _≀↷≀_ = {!!}
      }









