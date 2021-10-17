
module Verification.Experimental.Data.FinR.Definition where

open import Verification.Conventions


data _≤-⧜-ℕ_ : ∀(m n : ℕ) -> 𝒰₀ where
  instance zero : ∀{m} -> zero ≤-⧜-ℕ m
  instance suc : ∀{m n} -> {{_ : m ≤-⧜-ℕ n}} -> suc m ≤-⧜-ℕ suc n

fromNat-Fin-R : ∀{n} -> ∀(m : ℕ) -> {{_ : suc m ≤-⧜-ℕ n}} -> Fin-R n
fromNat-Fin-R zero {{suc}} = zero
fromNat-Fin-R (suc m) {{suc}} = suc (fromNat-Fin-R m)


instance
  HasFromNat:Fin-R : ∀{n} -> HasFromNat (Fin-R n)
  HasFromNat:Fin-R {n} = record { Constraint = (λ m -> suc m ≤-⧜-ℕ n) ; fromNat = fromNat-Fin-R }



-- module VEDFD where
--   private
--     lem-10 : ∀{m n} -> m ≤-ℕ (m +-ℕ n)
--     lem-10 {m} {n} = n , comm-+-ℕ n m
--     <-k+ : ∀{m n k} -> m <-ℕ n -> k +-ℕ m <-ℕ k +-ℕ n
--     <-k+ {m} {n} {k} p =
--       let q : k +-ℕ (suc m) ≤-ℕ k +-ℕ n
--           q = ≤-k+ p
--       in transport (λ i -> +-suc k m i ≤-ℕ k +-ℕ n) q

--     lem-20 : ∀{m n o} -> (n ≤-ℕ m) -> m ≡ n +-ℕ o -> m ∸ n ≡ o
--     lem-20 {zero} {zero} {o} p1 p2 = p2
--     lem-20 {zero} {suc n} {o} p1 p2 = {!!}
--     lem-20 {suc m} {zero} {o} p1 p2 = p2
--     lem-20 {suc m} {suc n} {o} p1 p2 = {!!}

--     lem-30 : ∀{m n} -> (n ≤-ℕ m) -> suc (m ∸ n) ≡ suc m ∸ n
--     lem-30 = {!!}

--   private
--     f0 : ∀{m n} -> Fin m -> Fin (m +-ℕ n)
--     f0 {m} {n} (i , ip) = i , trans-≤-ℕ ip lem-10

--     f1 : ∀{m n} -> Fin n -> Fin (m +-ℕ n)
--     f1 {m} {n} (i , ip) = (m +-ℕ i) , <-k+ ip

--     f : ∀{m n} -> Fin m +-𝒰 Fin n -> Fin (m +-ℕ n)
--     f (left x) = f0 x
--     f (just x) = f1 x

--     g : ∀{m n} -> Fin (m +-ℕ n) -> Fin m +-𝒰 Fin n
--     g {m} {n} (x , xp) with x ≟-ℕ m
--     ... | lt x<m = left (x , x<m)
--     ... | eq x₁ = right (0 , {!!})
--     ... | gt m<x = right (x ∸ m , 0 , lem-30 {x} {m} {!!} ∙ (lem-20 {suc x} {m} {n} {!!} {!!}))




