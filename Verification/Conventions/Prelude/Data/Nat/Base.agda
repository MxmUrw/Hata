
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.Nat.Base where
--

module Verification.Conventions.Prelude.Data.Nat.Base where

open import Verification.Conventions.Proprelude.CubicalConventions

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ; _-_ to _∸_)

open import Verification.Conventions.Prelude.Data.Nat.Literals public

predℕ : ℕ → ℕ
predℕ zero = zero
predℕ (suc n) = n

caseNat : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → ℕ → A
caseNat a0 aS zero    = a0
caseNat a0 aS (suc n) = aS

doubleℕ : ℕ → ℕ
doubleℕ zero = zero
doubleℕ (suc x) = suc (suc (doubleℕ x))

-- doublesℕ n m = 2^n * m
doublesℕ : ℕ → ℕ → ℕ
doublesℕ zero m = m
doublesℕ (suc n) m = doublesℕ n (doubleℕ m)

-- iterate
iter : ∀ {ℓ} {A : Type ℓ} → ℕ → (A → A) → A → A
iter zero f z    = z
iter (suc n) f z = f (iter n f z)

elim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → A zero
  → ((n : ℕ) → A n → A (suc n))
  → (n : ℕ) → A n
elim a₀ _ zero = a₀
elim a₀ f (suc n) = f n (elim a₀ f n)
