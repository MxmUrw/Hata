
module Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Rule where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Data.Universe.Everything
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

    hasActionₗ:Rule-⦿ : hasActionₗ (𝖢-⦿ A) (𝖱-⦿ A)
    hasActionₗ:Rule-⦿ = record
      { _↷_ = _↷-Rule-⦿_
      ; assoc-l-↷ = {!!}
      ; _≀↷≀_ = {!!}
      }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-Rule-⦿ : (f : A -> B) -> Rule-⦿ A -> Rule-⦿ B
  map-Rule-⦿ f (Μ ⊩ 𝔧) = map-Ctx-⦿ (map-Jdg-⦿ f) Μ ⊩ map-Jdg-⦿ f 𝔧

instance
  isFunctor:Rule-⦿ : isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖) (Rule-⦿)
  isFunctor.map isFunctor:Rule-⦿ = map-Rule-⦿
  isFunctor.isSetoidHom:map isFunctor:Rule-⦿ = {!!}
  isFunctor.functoriality-id isFunctor:Rule-⦿ = {!!}
  isFunctor.functoriality-◆ isFunctor:Rule-⦿ = {!!}

