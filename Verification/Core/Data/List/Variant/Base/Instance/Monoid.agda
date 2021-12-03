
module Verification.Core.Data.List.Variant.Base.Instance.Monoid where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Base.Definition

-- [Example]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  module ListProofs where

    -- | The |<>| operation on lists is unital.
    lem-1 : ∀{a : List A} -> a <> [] ≣ a
    lem-1 {[]} = refl-≣
    lem-1 {x ∷ a} = cong₂-Str _∷_ refl-≣ lem-1

    -- | And it is associative.
    lem-2 : ∀{a b c : List A} -> (a <> b) <> c ≣ a <> (b <> c)
    lem-2 {[]} = refl-≣
    lem-2 {x ∷ a} = cong₂-Str _∷_ refl-≣ (lem-2 {a})

  open ListProofs

  instance
    -- | This means that lists are a monoid.
    isMonoid:List : isMonoid ′(List A)′
    isMonoid:List = record
                      { _⋆_ = _<>_
                      ; ◌ = []
                      ; unit-l-⋆ = refl
                      ; unit-r-⋆ = lem-1
                      ; assoc-l-⋆ = λ {a} {b} {c} -> lem-2 {a} {b} {c}
                      ; _≀⋆≀_ = {!!}
                      }

-- //

-- [Hide]

module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-List : (f : A -> B) -> List A -> B
  rec-List f [] = ◌
  rec-List f (a ∷ as) = f a ⋆ rec-List f as

  instance
    Notation:hasRec:List : Notation:hasRec (A -> B) (List A -> B)
    Notation:hasRec:List = record { rec = rec-List }

-- //

