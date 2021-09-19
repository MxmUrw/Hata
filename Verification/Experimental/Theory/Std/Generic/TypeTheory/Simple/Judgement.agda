
module Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Data.Universe.Everything
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

    hasActionₗ:Jdg-⦿ : hasActionₗ (𝖢-⦿ A) (𝖩-⦿ A)
    hasActionₗ:Jdg-⦿ = record
      { _↷_ = _↷-Jdg-⦿_
      ; assoc-l-↷ = {!!}
      ; _≀↷≀_ = {!!}
      }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-Jdg-⦿ : (f : A -> B) -> Jdg-⦿ A -> Jdg-⦿ B
  map-Jdg-⦿ f (Γ ⊢ α) = map-Ctx-⦿ f Γ ⊢ f α

instance
  isFunctor:Jdg-⦿ : isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖) (Jdg-⦿)
  isFunctor.map isFunctor:Jdg-⦿ = map-Jdg-⦿
  isFunctor.isSetoidHom:map isFunctor:Jdg-⦿ = {!!}
  isFunctor.functoriality-id isFunctor:Jdg-⦿ = {!!}
  isFunctor.functoriality-◆ isFunctor:Jdg-⦿ = {!!}







