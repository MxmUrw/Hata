
module Verification.Experimental.Algebra.Monoid.Free.Definition where


open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Free
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


data Free-𝐌𝐨𝐧 (A : 𝒰 𝑖) : 𝒰 𝑖 where
  incl : A -> Free-𝐌𝐨𝐧 A
  _⋆-Free-𝐌𝐨𝐧_ : (a b : Free-𝐌𝐨𝐧 A) -> Free-𝐌𝐨𝐧 A
  ◌-Free-𝐌𝐨𝐧 : Free-𝐌𝐨𝐧 A




macro
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 : (A : 𝒰 𝑖) -> SomeStructure
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A = #structureOn (Free-𝐌𝐨𝐧 A)

module _ {A : 𝒰 𝑖} where

  infix 10 _∼-Free-𝐌𝐨𝐧_
  data _∼-Free-𝐌𝐨𝐧_ : (a b : Free-𝐌𝐨𝐧 A) -> 𝒰 𝑖 where
    unit-l-⋆-Free-𝐌𝐨𝐧  : ∀{a} -> ◌-Free-𝐌𝐨𝐧 ⋆-Free-𝐌𝐨𝐧 a ∼-Free-𝐌𝐨𝐧 a
    unit-r-⋆-Free-𝐌𝐨𝐧  : ∀{a} -> a ⋆-Free-𝐌𝐨𝐧 ◌-Free-𝐌𝐨𝐧 ∼-Free-𝐌𝐨𝐧 a
    assoc-l-⋆-Free-𝐌𝐨𝐧 : ∀{a b c} -> (a ⋆-Free-𝐌𝐨𝐧 b) ⋆-Free-𝐌𝐨𝐧 c ∼-Free-𝐌𝐨𝐧 a ⋆-Free-𝐌𝐨𝐧 (b ⋆-Free-𝐌𝐨𝐧 c)
    cong-l-⋆-Free-𝐌𝐨𝐧  : ∀{a b c} -> (a ∼-Free-𝐌𝐨𝐧 b) -> (a ⋆-Free-𝐌𝐨𝐧 c ∼-Free-𝐌𝐨𝐧 b ⋆-Free-𝐌𝐨𝐧 c)
    cong-r-⋆-Free-𝐌𝐨𝐧  : ∀{a b c} -> (b ∼-Free-𝐌𝐨𝐧 c) -> (a ⋆-Free-𝐌𝐨𝐧 b ∼-Free-𝐌𝐨𝐧 a ⋆-Free-𝐌𝐨𝐧 c)

  private
    lem-1 : ∀{a c d} ->  (q : RST _∼-Free-𝐌𝐨𝐧_ c d) -> RST _∼-Free-𝐌𝐨𝐧_ (a ⋆-Free-𝐌𝐨𝐧 c) (a ⋆-Free-𝐌𝐨𝐧 d)
    lem-1 (incl x) = incl (cong-r-⋆-Free-𝐌𝐨𝐧 x)
    lem-1 refl-RST = refl-RST
    lem-1 (sym-RST q) = sym-RST (lem-1 q)
    lem-1 (p ∙-RST q) = lem-1 p ∙-RST lem-1 q

  cong-⋆-Free-𝐌𝐨𝐧 : ∀{a b c d} -> (p : RST _∼-Free-𝐌𝐨𝐧_ a b) (q : RST _∼-Free-𝐌𝐨𝐧_ c d) -> RST _∼-Free-𝐌𝐨𝐧_ (a ⋆-Free-𝐌𝐨𝐧 c) (b ⋆-Free-𝐌𝐨𝐧 d)
  cong-⋆-Free-𝐌𝐨𝐧 (incl x) q     = incl (cong-l-⋆-Free-𝐌𝐨𝐧 x) ∙-RST lem-1 q
  cong-⋆-Free-𝐌𝐨𝐧 refl-RST q     = lem-1 q
  cong-⋆-Free-𝐌𝐨𝐧 (sym-RST p) q  = sym-RST (cong-⋆-Free-𝐌𝐨𝐧 p (sym-RST q))
  cong-⋆-Free-𝐌𝐨𝐧 (p ∙-RST p') q = cong-⋆-Free-𝐌𝐨𝐧 p q ∙-RST cong-⋆-Free-𝐌𝐨𝐧 p' refl-RST

  instance
    isSetoid:Free-𝐌𝐨𝐧 : isSetoid (Free-𝐌𝐨𝐧 A)
    isSetoid:Free-𝐌𝐨𝐧 = isSetoid:byFree _∼-Free-𝐌𝐨𝐧_

    isMonoid:Free-𝐌𝐨𝐧 : isMonoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isMonoid:Free-𝐌𝐨𝐧 = record
                          { _⋆_        = _⋆-Free-𝐌𝐨𝐧_
                          ; ◌          = ◌-Free-𝐌𝐨𝐧
                          ; unit-l-⋆   = incl unit-l-⋆-Free-𝐌𝐨𝐧
                          ; unit-r-⋆   = incl unit-r-⋆-Free-𝐌𝐨𝐧
                          ; assoc-l-⋆  = incl assoc-l-⋆-Free-𝐌𝐨𝐧
                          ; _`cong-⋆`_ = cong-⋆-Free-𝐌𝐨𝐧
                          }

  data _∍_ : A -> Free-𝐌𝐨𝐧 A -> 𝒰 𝑖 where
    incl : ∀{x} -> x ∍ incl x
    left-∍ : ∀{a b x} -> x ∍ a -> x ∍ (a ⋆ b)
    right-∍ : ∀{a b x} -> x ∍ b -> x ∍ (a ⋆ b)

module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-Free-𝐌𝐨𝐧 : (f : A -> B) -> Free-𝐌𝐨𝐧 A -> B
  rec-Free-𝐌𝐨𝐧 f (incl x)           = f x
  rec-Free-𝐌𝐨𝐧 f (a ⋆-Free-𝐌𝐨𝐧 b)  = rec-Free-𝐌𝐨𝐧 f a ⋆ rec-Free-𝐌𝐨𝐧 f b
  rec-Free-𝐌𝐨𝐧 f ◌-Free-𝐌𝐨𝐧        = ◌

  instance
    Notation:hasRec:Free-𝐌𝐨𝐧 : Notation:hasRec (A -> B) (Free-𝐌𝐨𝐧 A -> B)
    Notation:hasRec:Free-𝐌𝐨𝐧 = record { rec = rec-Free-𝐌𝐨𝐧 }


