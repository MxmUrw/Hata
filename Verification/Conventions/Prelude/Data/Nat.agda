
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.Nat where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes

instance
  IShow:ℕ : IShow ℕ
  IShow.show IShow:ℕ = primShowNat

  IBootEq:ℕ : IBootEq ℕ
  (IBootEq._≟_ IBootEq:ℕ) a b with a ≟-ℕ b
  ... | lt x = false
  ... | eq x = true
  ... | gt x = false


data _≤-ℕ-Dec_ : ℕ -> ℕ -> 𝒰₀ where
  instance zero : ∀{n} -> zero ≤-ℕ-Dec n
  instance suc : ∀{m n} -> {{_ : m ≤-ℕ-Dec n}} -> suc m ≤-ℕ-Dec suc n

≤→Fin : ∀{a b} -> {{_ : a ≤-ℕ-Dec b}} -> (Fin-R (suc b))
≤→Fin {a = zero} {{p}} = zero
≤→Fin {a = suc a} {.(suc _)} {{suc {{p}}}} = suc (≤→Fin {{p}})

-- instance
--   Cast:≤,Fin : ∀{a b} -> Cast (a ≤-ℕ-Dec b) (Fin (suc b))
--   Cast:≤,Fin = newcast ≤→Fin


