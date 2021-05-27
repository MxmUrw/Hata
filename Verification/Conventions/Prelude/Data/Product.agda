
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.Product where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.String
open import Verification.Conventions.Prelude.Data.Maybe
open import Verification.Conventions.Prelude.Data.Nat

variable m n k : ℕ

instance
  IShow:× : ∀{A B : 𝒰 𝑖} -> {{_ : IShow A}} {{_ : IShow B}} -> IShow (A ×-𝒰 B)
  IShow.show IShow:× (a , b) = "(" <> show a <> " , " <> show b <> ")"


_^-𝒰_ : 𝒰 𝑖 -> ℕ -> 𝒰 𝑖
A ^-𝒰 zero = Lift 𝟙-𝒰
A ^-𝒰 suc zero = A
A ^-𝒰 suc (suc n) = A ×-𝒰 (A ^-𝒰 (suc n))

_⌄-𝒰_ : ∀{A : 𝒰 𝑖} -> {n : ℕ} -> (A ^-𝒰 suc n) -> Fin-R (suc n) -> A
_⌄-𝒰_ {n = zero} x zero = x
_⌄-𝒰_ {n = suc n} (x , xs) zero = x
_⌄-𝒰_ {n = suc n} (x , xs) (suc i) = _⌄-𝒰_ xs i


instance
  Exponent-Notation:𝒰,ℕ,𝒰 : Exponent-Notation (𝒰 𝑖) ℕ (∆ (𝒰 𝑖))
  (Exponent-Notation:𝒰,ℕ,𝒰 Exponent-Notation.^ x) n = _^-𝒰_ x n

_⌄E_ : ∀{A : 𝒰 𝑖} -> ∀{n} -> (A ^ (suc n)) -> (i : ℕ) -> {{_ : i ≤-ℕ-Dec n}} -> (A)
_⌄E_ x i {{p}} = x ⌄-𝒰 (≤→Fin {{p}})

instance
  Index-Notation:^-𝒰,ℕ,A : ∀{A : 𝒰 𝑖} -> ∀{n} -> Index-Notation (A ^ (suc n)) (∆ ℕ) (λ i -> i ≤-ℕ-Dec n) (∆ A)
  Index-Notation._⌄_ Index-Notation:^-𝒰,ℕ,A x i {{p}} = x ⌄E i


-- GetMy : ∀{A : 𝒰 𝑖} -> A ^ 2 -> A
-- GetMy a = a ⌄ 1


-- getfst : ∀{n} -> (i : ℕ) -> {{_ : i ≤-ℕ-Dec n}} -> 𝔏 ^ (suc n) -> 𝔏
-- getfst i l = l ⌄ i

-- getfst2 : ∀{ℓ : 𝔏} -> {A : 𝒰 ℓ} -> ∀{n} -> (i : ℕ) -> {{_ : i ≤-ℕ-Dec n}} -> A ^ (suc n) -> A
-- getfst2 i l = l ⌄ i


-- record MyRec (ls : 𝔏 ^ 3) : 𝒰 (merge ls ⁺) where
--   field Test2 : 𝒰' (ls ⌄ 0)

