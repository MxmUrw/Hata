
module Verification.Experimental.Algebra.Monoid.Free where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Algebra.Monoid.Definition

pattern ⦋⦌ = []
pattern ⦋_⦌ a = a ∷ []
pattern ⦋_،_⦌ a b = a ∷ b ∷ []
pattern ⦋_،_،_⦌ a b c = a ∷ b ∷ c ∷ []
pattern ⦋_،_،_،_⦌ a b c d = a ∷ b ∷ c ∷ d ∷ []
pattern ⦋_،_،_،_،_⦌ a b c d e = a ∷ b ∷ c ∷ d ∷ e ∷ []

cong₂-Str : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> (f : A -> B -> C) -> {a1 a2 : A} -> {b1 b2 : B} -> (p : a1 ≣ a2) -> (q : b1 ≣ b2) -> f a1 b1 ≣ f a2 b2
cong₂-Str f refl-≣ refl-≣ = refl-≣

module _ {A : 𝒰 𝑖} where

  instance
    isSetoid:List : isSetoid (List A)
    isSetoid:List = isSetoid:byStrId


  aaaa = cong₂


  module ListProofs where
    lem-1 : ∀{a : List A} -> a <> ⦋⦌ ≣ a
    lem-1 {⦋⦌} = refl-≣
    lem-1 {x ∷ a} = cong₂-Str _∷_ refl-≣ lem-1

    lem-2 : ∀{a b c : List A} -> (a <> b) <> c ≣ a <> (b <> c)
    lem-2 {⦋⦌} = refl-≣
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


