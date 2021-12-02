
module Verification.Core.Data.List.Instance.Monoid where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Definition

module _ {A : 𝒰 𝑖} where
  module ListProofs where
    lem-1 : ∀{a : List A} -> a <> [] ≣ a
    lem-1 {[]} = refl-≣
    lem-1 {x ∷ a} = cong₂-Str _∷_ refl-≣ lem-1

    lem-2 : ∀{a b c : List A} -> (a <> b) <> c ≣ a <> (b <> c)
    lem-2 {[]} = refl-≣
    lem-2 {x ∷ a} = cong₂-Str _∷_ refl-≣ (lem-2 {a})

  open ListProofs

  instance
    isMonoid:List : isMonoid ′(List A)′
    isMonoid:List = record
                      { _⋆_ = _<>_
                      ; ◌ = []
                      ; unit-l-⋆ = refl
                      ; unit-r-⋆ = lem-1
                      ; assoc-l-⋆ = λ {a} {b} {c} -> lem-2 {a} {b} {c}
                      ; _≀⋆≀_ = {!!}
                      }

module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-List : (f : A -> B) -> List A -> B
  rec-List f [] = ◌
  rec-List f (a ∷ as) = f a ⋆ rec-List f as

  instance
    Notation:hasRec:List : Notation:hasRec (A -> B) (List A -> B)
    Notation:hasRec:List = record { rec = rec-List }

