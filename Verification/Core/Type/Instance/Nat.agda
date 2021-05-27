
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Type.Instance.Nat where

open import Verification.Conventions
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Partialorder
open import Verification.Core.Order.Instance.Level

split-ℕ : (n : ℕ) -> (n ≡ 0) +-𝒰 (∑ λ m -> n ≡ suc m)
split-ℕ zero = left refl
split-ℕ (suc n) = right (n , refl)

max-ℕ : (m n : ℕ) -> ℕ
max-ℕ zero n = n
max-ℕ (suc m) zero = suc m
max-ℕ (suc m) (suc n) = suc (max-ℕ m n)


-- Preorder:ℕ : Preorder ⊥
-- ⟨ Preorder:ℕ ⟩ = ℕ
-- IPreorder._≤_ (of Preorder:ℕ) = _≤-ℕ_
-- IPreorder.refl-≤ (of Preorder:ℕ) = ≤-ℕ-refl
-- IPreorder.trans-≤ (of Preorder:ℕ) = ≤-ℕ-trans

-- instance IPreorder:ℕ = #openstruct Preorder:ℕ


