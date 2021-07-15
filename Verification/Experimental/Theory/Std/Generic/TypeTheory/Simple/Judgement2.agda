
module Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2 where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Context


record Judgement (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _⊢_
  field fst : List A
  field snd : A
open Judgement

infix 30 _⊢_

module _ (A : 𝒰 𝑖) where
  macro Jdg = #structureOn (Judgement A)

private
  module _ {A : 𝒰 𝑖} where
    _↷-Jdg_ : (List A) -> (Jdg A) -> (Jdg A)
    _↷-Jdg_ Γ (Δ ⊢ α) = (Γ ⋆ Δ ⊢ α)




module _ {A : 𝒰 𝑖} where
  infix 3 _⊨-var_
  data _⊨-var_ : List A -> A -> 𝒰 𝑖 where
    zero : ∀{Γ α} -> α ∷ Γ ⊨-var α
    suc  : ∀{Γ α β} -> Γ ⊨-var β -> α ∷ Γ ⊨-var β

  instance
    isSetoid:Jdg : isSetoid (Jdg A)
    isSetoid:Jdg = isSetoid:byPath

    hasAction-l:Jdg : hasAction-l ′(List A)′ (Jdg A)
    hasAction-l:Jdg = record
      { _↷_ = _↷-Jdg_
      ; assoc-l-↷ = {!!}
      ; _≀↷≀_ = {!!}
      }

    hasAction-l:JdgList : hasAction-l ′(List A)′ ′ List(Jdg A)′
    hasAction-l:JdgList = record
      { _↷_ = λ Γ xs -> map-List (Γ ↷_) xs
      ; assoc-l-↷ = {!!}
      ; _≀↷≀_ = {!!}
      }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-Jdg : (f : A -> B) -> Jdg A -> Jdg B
  map-Jdg f (Γ ⊢ α) = map-List f Γ ⊢ f α

instance
  isFunctor:Jdg : isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖) (Judgement)
  isFunctor.map isFunctor:Jdg = map-Jdg
  isFunctor.isSetoidHom:map isFunctor:Jdg = {!!}
  isFunctor.functoriality-id isFunctor:Jdg = {!!}
  isFunctor.functoriality-◆ isFunctor:Jdg = {!!}


instance
  isFunctorList : isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖) (List)
  isFunctor.map isFunctorList = map-List
  isFunctor.isSetoidHom:map isFunctorList = {!!}
  isFunctor.functoriality-id isFunctorList = {!!}
  isFunctor.functoriality-◆ isFunctorList = {!!}


