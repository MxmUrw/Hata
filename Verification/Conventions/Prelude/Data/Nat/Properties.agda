
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.Nat.Properties where
--

module Verification.Conventions.Prelude.Data.Nat.Properties where

open import Verification.Conventions.Proprelude.CubicalConventions
open import Verification.Conventions.Prelude.Data.Nat.Base
open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Data.StrictId
open import Verification.Conventions.Prelude.Classes.EquivalenceRelation
open import Verification.Conventions.Prelude.Classes.Setoid
open import Verification.Conventions.Prelude.Classes.Discrete

private
  ⊥ = 𝟘-𝒰

-- open import Cubical.Core.Everything

-- open import Cubical.Foundations.Prelude

-- open import Cubical.Data.Nat.Base
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Sigma

-- open import Cubical.Relation.Nullary
-- open import Cubical.Relation.Nullary.DecidableEq

private
  variable
    l m n : ℕ

instance
  isSetoid:ℕ : isSetoid ℕ
  isSetoid:ℕ = isSetoid:byId

znots : ¬ (0 ≣ suc n)
znots eq = subst-Str (caseNat ℕ ⊥) eq 0

snotz : ¬ (suc n ≣ 0)
snotz eq = subst-Str (caseNat ⊥ ℕ) eq 0

injSuc : suc m ≣ suc n → m ≣ n
injSuc p = cong-Str predℕ p

discreteℕ : Discrete ℕ
discreteℕ zero zero = yes refl
discreteℕ zero (suc n) = no znots
discreteℕ (suc m) zero = no snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
... | yes p = yes (cong-Str suc p)
... | no p = no (λ x → p (injSuc x))

-- isSetℕ : isSet ℕ
-- isSetℕ = Discrete→isSet discreteℕ

-- Arithmetic facts about predℕ

suc-predℕ : ∀ (n : ℕ) → ¬ (n ≣ 0) → n ≣ suc (predℕ n)
suc-predℕ zero p = 𝟘-rec (p refl)
suc-predℕ (suc n) p = refl

-- Arithmetic facts about +

+-zero : ∀ m → m + 0 ≣ m
+-zero zero = refl
+-zero (suc m) = cong-Str suc (+-zero m)

+-suc : ∀ m n → m + suc n ≣ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong-Str suc (+-suc m n)

+-comm : ∀ m n → m + n ≣ n + m
+-comm m zero = +-zero m
+-comm m (suc n) = (+-suc m n) ∙ (cong-Str suc (+-comm m n))

-- Addition is associative
+-assoc : ∀ m n o → m + (n + o) ≣ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong-Str suc (+-assoc m n o)

inj-m+ : m + l ≣ m + n → l ≣ n
inj-m+ {zero} p = p
inj-m+ {suc m} p = inj-m+ (injSuc p)

inj-+m : l + m ≣ n + m → l ≣ n
inj-+m {l} {m} {n} p = inj-m+ ((+-comm m l) ∙ (p ∙ (+-comm n m)))

m+n≣n→m≣0 : m + n ≣ n → m ≣ 0
m+n≣n→m≣0 {n = zero} = λ p → (sym (+-zero _)) ∙ p
m+n≣n→m≣0 {n = suc n} p = m+n≣n→m≣0 (injSuc ((sym (+-suc _ n)) ∙ p))

m+n≣0→m≣0×n≣0 : m + n ≣ 0 → (m ≣ 0) × (n ≣ 0)
m+n≣0→m≣0×n≣0 {zero} = refl ,_
m+n≣0→m≣0×n≣0 {suc m} p = 𝟘-rec (snotz p)

-- Arithmetic facts about *

0≣m*0 : ∀ m → 0 ≣ m * 0
0≣m*0 zero = refl
0≣m*0 (suc m) = 0≣m*0 m

*-suc : ∀ m n → m * suc n ≣ m + m * n
*-suc zero n = refl
*-suc (suc m) n
  = cong-Str suc
  ( n + m * suc n ≣⟨ cong-Str (n +_) (*-suc m n) ⟩
    n + (m + m * n) ≣⟨ +-assoc n m (m * n) ⟩
    (n + m) + m * n ≣⟨ cong-Str (_+ m * n) (+-comm n m) ⟩
    (m + n) + m * n ≣⟨ sym (+-assoc m n (m * n)) ⟩
    m + (n + m * n) ∎
  )

*-comm : ∀ m n → m * n ≣ n * m
*-comm zero n = 0≣m*0 n
*-comm (suc m) n = cong-Str (n +_) (*-comm m n) ∙ sym (*-suc n m)

*-distribʳ : ∀ m n o → (m * o) + (n * o) ≣ (m + n) * o
*-distribʳ zero _ _ = refl
*-distribʳ (suc m) n o = sym (+-assoc o (m * o) (n * o)) ∙ cong-Str (o +_) (*-distribʳ m n o)

-- *-distribˡ : ∀ o m n → (o * m) + (o * n) ≣ o * (m + n)
-- *-distribˡ o m n = (λ i → *-comm o m i + *-comm o n i) ∙ *-distribʳ m n o ∙ *-comm (m + n) o

*-assoc : ∀ m n o → m * (n * o) ≣ (m * n) * o
*-assoc zero _ _ = refl
*-assoc (suc m) n o = cong-Str (n * o +_) (*-assoc m n o) ∙ *-distribʳ n (m * n) o

*-identityˡ : ∀ m → 1 * m ≣ m
*-identityˡ m = +-zero m

*-identityʳ : ∀ m → m * 1 ≣ m
*-identityʳ zero = refl
*-identityʳ (suc m) = cong-Str suc (*-identityʳ m)

0≣n*sm→0≣n : 0 ≣ n * suc m → 0 ≣ n
0≣n*sm→0≣n {n = zero} p = refl
0≣n*sm→0≣n {n = suc n} p = 𝟘-rec (znots p)

inj-*sm : l * suc m ≣ n * suc m → l ≣ n
inj-*sm {zero} {m} {n} p = 0≣n*sm→0≣n p
inj-*sm {l} {m} {zero} p = sym (0≣n*sm→0≣n (sym p))
inj-*sm {suc l} {m} {suc n} p = cong-Str suc (inj-*sm (inj-m+ {m = suc m} p))

inj-sm* : suc m * l ≣ suc m * n → l ≣ n
inj-sm* {m} {l} {n} p = inj-*sm (*-comm l (suc m) ∙ p ∙ *-comm (suc m) n)

-- Arithmetic facts about ∸

zero∸ : ∀ n → zero ∸ n ≣ zero
zero∸ zero = refl
zero∸ (suc _) = refl

∸-cancelˡ : ∀ k m n → (k + m) ∸ (k + n) ≣ m ∸ n
∸-cancelˡ zero    = λ _ _ → refl
∸-cancelˡ (suc k) = ∸-cancelˡ k

-- ∸-cancelʳ : ∀ m n k → (m + k) ∸ (n + k) ≣ m ∸ n
-- ∸-cancelʳ m n k = (λ i → +-comm m k i ∸ +-comm n k i) ∙ ∸-cancelˡ k m n

∸-distribʳ : ∀ m n k → (m ∸ n) * k ≣ m * k ∸ n * k
∸-distribʳ m       zero    k = refl
∸-distribʳ zero    (suc n) k = sym (zero∸ (k + n * k))
∸-distribʳ (suc m) (suc n) k = ∸-distribʳ m n k ∙ sym (∸-cancelˡ k (m * k) (n * k))
