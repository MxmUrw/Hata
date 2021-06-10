
-- {-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Classes.EquivalenceRelation where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes.Operators.Unary
open import Verification.Conventions.Prelude.Classes.Cast
open import Verification.Conventions.Prelude.Classes.Anything
open import Verification.Conventions.Prelude.Data.StrictId


--------------------------------------------------------------------------------
-- == Equivalence relation
--

-- #Notation/Annotatable# trans
-- #Notation/SemanticCategory# \mathrm{Eqv} = Equiv

-- [Definition]
record isEquivRel {X : 𝒰 𝑖} (_≣_ : X -> X -> 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  constructor equivRel
  field refl : ∀{x : X} -> x ≣ x
        sym : ∀{x y : X} -> x ≣ y -> y ≣ x
        _∙_ : ∀{x y z : X} -> x ≣ y -> y ≣ z -> x ≣ z

  infixl 30 _∙_
open isEquivRel {{...}} public
-- //

module _ {X : 𝒰 𝑖} {_≣_ : X -> X -> 𝒰 𝑗} {{_ : isEquivRel _≣_}} where
  instance
    Notation-Inverse:Equiv : {x y : X} -> Notation-Inverse (x ≣ y) (y ≣ x)
    Notation-Inverse:Equiv Notation-Inverse.⁻¹ = sym


instance
-- module _ where
  isEquivRel:Path : {X : 𝒰 𝑖} -> isEquivRel (λ (x y : X) -> x ≡ y)
  isEquivRel.refl  isEquivRel:Path = refl-Path
  isEquivRel.sym   isEquivRel:Path = sym-Path
  isEquivRel._∙_   isEquivRel:Path = trans-Path


-- module _ {X : 𝒰 𝑖} (_∼_ : X -> X -> 𝒰 𝑗) where
--   record hasTransport : 𝒰 𝑗 where
--     field transport : ∀{a b : X} (a ∼ b) -> 



module _ {X : 𝒰 𝑖} {_∼_ : X -> X -> 𝒰 𝑗} {{_ : isEquivRel _∼_}} where
  fromPath : ∀{a b : X} -> a ≡ b -> a ∼ b
  fromPath {a = a} p = transport (λ i -> a ∼ p i) refl

-- sym-Id : ∀{X : 𝒰 𝑖} {x y : X} -> Id x y -> Id y x
-- sym-Id {x = x} {y = y} p = J-Id (λ y _ -> Id y x) refl-Id p

{-
trans-Id : ∀{X : 𝒰 𝑖} {x y z : X} -> Id x y -> Id y z -> Id x z
trans-Id {x = x} {y} {z} p q = J-Id (λ z _ -> Id x z) p q

instance
-- module _ where
  isEquivRel:Id : {X : 𝒰 𝑖} -> isEquivRel (λ (x y : X) -> Id x y)
  isEquivRel.refl isEquivRel:Id = refl-Id
  isEquivRel.sym isEquivRel:Id = sym-Id
  isEquivRel._∙_ isEquivRel:Id = trans-Id

module _ {X : 𝒰 𝑘} {x : X} where
  record ∀Id (P : (y : X) -> Id x y -> 𝒰 𝑙) : 𝒰 (𝑘 ⊔ 𝑙) where
    constructor idproof
    field getProof : ∀{y : X} -> (p : Id x y) -> P y p

  open ∀Id public

  J-∀Id : ∀{P : (y : X) -> Id x y -> 𝒰 𝑙} -> (d : P x refl-Id) -> ∀Id P
  J-∀Id {P = P} d = idproof $ λ p -> (J-Id P d p)

cong₂-Id-helper : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> {a1 : A} {b1 : B} -> (f : A -> B -> C)
                 -> ∀Id (λ a2 (p : Id a1 a2) -> ∀Id (λ b2 (q : Id b1 b2) -> Id (f a1 b1) (f a2 b2)))
cong₂-Id-helper f = J-∀Id (J-∀Id refl-Id)

cong₂-Id : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> {a1 a2 : A} {b1 b2 : B} -> (f : A -> B -> C) -> (Id a1 a2) -> (Id b1 b2) -> Id (f a1 b1) (f a2 b2)
cong₂-Id f p q = cong₂-Id-helper f .getProof p .getProof q
-}

instance
-- module _ where
  isEquivRel:StrId : {X : 𝒰 𝑖} -> isEquivRel (λ (x y : X) -> StrId x y)
  isEquivRel.refl isEquivRel:StrId = refl-StrId
  isEquivRel.sym isEquivRel:StrId refl-StrId = refl-StrId
  (isEquivRel:StrId isEquivRel.∙ refl-StrId) q = q


instance
  Cast:≡Str : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> Cast (a ≡-Str b) IAnything (a ≡ b)
  Cast.cast Cast:≡Str refl-StrId = refl-Path

≡-Str→≡ : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (a ≡-Str b) -> (a ≡ b)
≡-Str→≡ refl-StrId = refl-Path

≡→≡-Str : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (a ≡ b) -> (a ≡-Str b)
≡→≡-Str {a = a} {b} p = transport (λ i -> a ≡-Str (p i)) refl-StrId

-- right≢left-Str : ∀{a : A}

≡-change-iso : ∀{X : 𝒰 𝑖} -> ∀{a b : X} -> (p : a ≡-Str b) -> (≡→≡-Str (≡-Str→≡ p) ≡ p)
≡-change-iso refl-StrId = transportRefl refl-StrId

--------------------------------------------------------------------------------
-- === path syntax

module _ {A : 𝒰 𝑖} {_≣_ : A -> A -> 𝒰 𝑗} {{_ : isEquivRel _≣_}} where
  _≣⟨_⟩_ : (x : A) {y : A} {z : A} → x ≣ y → y ≣ z → x ≣ z
  _ ≣⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

  ≣⟨⟩-syntax : (x : A) {y z : A} → x ≣ y → y ≣ z → x ≣ z
  ≣⟨⟩-syntax = _≣⟨_⟩_
  infixr 2 ≣⟨⟩-syntax
  infix  3 _∎
  infixr 2 _≣⟨_⟩_

  _∎ : (x : A) → x ≣ x
  _ ∎ = refl


-- new syntax with ∼
module _ {A : 𝒰 𝑖} {_∼_ : A -> A -> 𝒰 𝑗} {{_ : isEquivRel _∼_}} where
  _⟨_⟩-∼_ : (x : A) {y : A} {z : A} → x ∼ y → y ∼ z → x ∼ z
  _ ⟨ x≡y ⟩-∼ y≡z = x≡y ∙ y≡z

  ⟨⟩-∼-syntax : (x : A) {y z : A} → x ∼ y → y ∼ z → x ∼ z
  ⟨⟩-∼-syntax = _⟨_⟩-∼_
  infixr 2 ⟨⟩-∼-syntax
  infixr 2 _⟨_⟩-∼_

  infix  3 _∎-∼

  _∎-∼ : (x : A) → x ∼ x
  _ ∎-∼ = refl



