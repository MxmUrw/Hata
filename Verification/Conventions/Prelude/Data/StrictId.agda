
-- {-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.StrictId where

open import Verification.Conventions.Proprelude

data StrId {a} {A : 𝒰 a} (x : A) : A → 𝒰 a where
  instance refl-StrId : StrId x x

{-# BUILTIN EQUALITY StrId #-}

pattern refl-≣ = refl-StrId

infix 4 _≣_
_≣_ = StrId
_≡-Str_ = StrId


_≢-Str_ : ∀{X : 𝒰 𝑙} -> (a b : X) -> 𝒰 𝑙
a ≢-Str b = ¬ StrId a b

transport-Str : ∀{A B : 𝒰 𝑖} -> (p : A ≡-Str B) -> (a : A) -> B
transport-Str refl-StrId a = a

cong-Str : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {a b : A} -> (f : A -> B) -> (a ≡-Str b) -> (f a ≡-Str f b)
cong-Str f refl-StrId = refl-StrId

cong₂-Str : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {X : 𝒰 𝑘} {a b : A} {c d : B} -> (f : A -> B -> X) -> (a ≡-Str b) -> (c ≡-Str d) -> (f a c ≡-Str f b d)
cong₂-Str f refl-StrId refl-StrId = refl-StrId

subst-Str : ∀{A : 𝒰 𝑖} {x y : A} (B : A → 𝒰 𝑗) (p : x ≣ y) → B x → B y
subst-Str B p pa = transport-Str (cong-Str B p) pa

