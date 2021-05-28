

module Verification.Conventions.Prelude.Data.Nat where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.Bool

-- ** these are our non cubical replacements **
open import Verification.Conventions.Prelude.Data.Nat.Base renaming (_+_ to _+-ℕ_ ; _*_ to _*-ℕ_) public
open import Verification.Conventions.Prelude.Data.Nat.Properties renaming (znots to zero≢suc ; snotz to suc≢zero ; +-assoc to assoc-+-ℕ ; +-comm to comm-+-ℕ) public
open import Verification.Conventions.Prelude.Data.Nat.Order renaming (_≤_ to _≤-ℕ_ ; _<_ to _<-ℕ_ ; _≟_ to _≟-ℕ_ ; ≤-refl to refl-≤-ℕ ; ≤-trans to trans-≤-ℕ ; ≤-antisym to antisym-≤-ℕ) public

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

-- instance
--   Cast:≤,Fin : ∀{a b} -> Cast (a ≤-ℕ-Dec b) (Fin (suc b))
--   Cast:≤,Fin = newcast ≤→Fin


