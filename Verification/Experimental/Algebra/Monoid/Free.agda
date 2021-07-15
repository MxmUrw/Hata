
module Verification.Experimental.Algebra.Monoid.Free where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Algebra.Monoid.Definition

pattern ⦋⦌ = []
pattern ⦋_⦌ a = a ∷ []
-- pattern ⦋_،_⦌ a b = [] ,, a ,, b
-- pattern ⦋_،_،_⦌ a b c = [] ,, a ,, b ,, c

module _ {A : 𝒰 𝑖} where

  instance
    isSetoid:List : isSetoid (List A)
    isSetoid:List = isSetoid:byPath

  instance
    isMonoid:List : isMonoid ′(List A)′
    isMonoid:List = record
                      { _⋆_ = _<>_
                      ; ◌ = []
                      ; unit-l-⋆ = {!!}
                      ; unit-r-⋆ = {!!}
                      ; assoc-l-⋆ = {!!}
                      ; assoc-r-⋆ = {!!}
                      ; _`cong-⋆`_ = {!!}
                      }

record Notation:hasRec (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field rec : A -> B

open Notation:hasRec {{...}} public

module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-List : (f : A -> B) -> List A -> B
  rec-List f [] = ◌
  rec-List f (a ∷ as) = f a ⋆ rec-List f as

  instance
    Notation:hasRec:List : Notation:hasRec (A -> B) (List A -> B)
    Notation:hasRec:List = record { rec = rec-List }


