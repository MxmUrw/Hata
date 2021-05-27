
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.Vec where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.Nat
open import Verification.Conventions.Prelude.Data.Maybe

-- instance
--   Cast:A,Vec : ∀{A : 𝒰 𝑖} -> Cast A (Vec A 1)
--   Cast.cast Cast:A,Vec x = x ∷ []

-- infixl 45 _､_
-- _､_ : ∀{A B X : 𝒰 𝑖} -> ∀{m n} -> {{_ : Cast A (Vec X m)}} -> {{_ : Cast B (Vec X n)}} -> A -> B -> Vec X (m +-ℕ n)
-- x ､ y = cast x ++-Vec cast y

-- record LSize (A : 𝒰₀) (n : ℕ) : 𝒰₀ where

-- record _×L_ {m n} (A : 𝒰₀) {{_ : LSize A m}} (B : 𝒰₀) {{_ : LSize B n}} : 𝒰₀ where
--   constructor _,,_
--   field fst : A
--   field snd : B


-- 𝔏n : (n : ℕ) -> 𝒰₀

-- instance
--   𝔏n-Size : ∀{n} -> LSize (𝔏n n) n
--   𝔏n-Size = record {}

-- private
-- --   module Exp where
--   infixr 100 _^E_
--   -- _^E_ : 𝒰 𝑖 -> ℕ -> 𝒰 𝑖
--   _^E_ : 𝒰 𝑖 -> ℕ -> 𝒰 𝑖
--   A ^E zero = Lift ⊤
--   A ^E suc zero = A
--   A ^E suc (suc n) = A ×-𝒰 (A ^E (suc n))



-- 𝔏n n = 𝔏 ^E n
-- 𝔏n zero = ⊤
-- 𝔏n (suc zero) = 𝔏
-- 𝔏n (suc (suc n)) = 𝔏 ×-𝒰 𝔏n (suc n)


-- instance
  -- Index-Notation:Vec,ℕ,A : ∀{A : 𝒰 𝑖} -> ∀{n} -> Index-Notation (Vec A (suc n)) ℕ (just $ λ i -> i ≤-ℕ-Dec n) (∆ A)
  -- Index-Notation._⌄_ Index-Notation:Vec,ℕ,A x i {{p}} = lookup (cast p) x







-- myfunc : (aa : 𝔏n 1) -> 𝒰 _
-- myfunc aa = 𝒰 (aa ⌄ 0)

-- variable
--   n-a : ℕ
--   myvar : 𝔏n n-a

-- intoit : myfunc myvar -> 𝒰₀
-- intoit = {!!}

-- mytest : intoit ℓ₀
-- mytest = ?

-- mytest : ∀{v : Vec ℕ 1} -> (v ⌄ 0) ∷ [] ≡ v
-- mytest = {!!}



