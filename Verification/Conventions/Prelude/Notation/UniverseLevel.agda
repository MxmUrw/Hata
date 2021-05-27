
{-# OPTIONS --cubical --no-import-sorts #-}

module Verification.Conventions.Prelude.Notation.UniverseLevel where

open import Verification.Conventions.Proprelude hiding (𝒰) renaming (_⁺ to _⁺')
-- open import Verification.Conventions.Prelude.Data.Vec
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.Product
open import Verification.Conventions.Prelude.Data.Nat



-- merge : 𝔏 ^ n -> 𝔏
-- merge {n = zero} _ = ℓ₀
-- merge {n = suc zero} x = x
-- merge {n = suc (suc n)} (x , xs) = x ⊔ merge xs

  -- merge : Vec 𝔏 m -> 𝔏
  -- merge [] = ℓ₀
  -- merge (ℓ ∷ []) = ℓ
  -- merge (l ∷ j ∷ ls) = l ⊔ merge (j ∷ ls)

merge : ∀{n : ℕ} -> 𝔏 ^ n -> 𝔏
merge {n = zero} _ = ℓ₀
merge {n = suc zero} x = x
merge {n = suc (suc n)} (x , xs) = x ⊔ merge xs

instance
  IMultiJoinable:VecLevel : IMultiJoinable (𝔏 ^ m) 𝔏
  IMultiJoinable.⨆ IMultiJoinable:VecLevel = merge

-- instance
--   Cast:A,^ : ∀{A : 𝒰 𝑖} -> Cast A (A ^ 1)
--   Cast.cast Cast:A,^ a = a

-- instance
--   Cast:Ln,L : Cast (𝔏 ^ n) 𝔏
--   Cast:Ln,L = ⨆

-- _､_ : ∀{A B : 𝒰 𝑖} -> ∀{m n : ℕ} -> {{_ : Cast A (𝔏 ^ m)}} -> {{_ : Cast B (𝔏 ^ n)}} -> A -> B -> 𝔏
-- x ､ y = (merge (cast x)) ⊔ (merge (cast y))


infixl 45 _､_
_､_ : ∀{m n : ℕ} -> 𝔏 ^ m -> 𝔏 ^ n -> 𝔏
x ､ y = (merge (x)) ⊔ (merge (y))




record MergeLevel (A : 𝒰' 𝑖) : 𝒰' 𝑖 where
  field domerge : A -> 𝔏
open MergeLevel {{...}}

instance
  MergeLevel:𝔏^n,𝔏 : MergeLevel (𝔏 ^ n)
  MergeLevel.domerge MergeLevel:𝔏^n,𝔏 = merge


instance
  Cast:𝔏^n,𝔏 : Cast (𝔏 ^ n) IAnything 𝔏
  Cast.cast Cast:𝔏^n,𝔏 x = merge x

𝒰'' : ∀{A : 𝒰' 𝑖} -> {{_ : MergeLevel A}} -> (a : A) -> 𝒰' (domerge a ⁺')
𝒰'' a = 𝒰' (domerge a)

infix 50 _⁺
_⁺ : ∀{A : 𝒰' 𝑖} -> {{_ : MergeLevel A}} -> A -> 𝔏
_⁺ a = (domerge a) ⁺'


  -- Cast:𝔏^n,𝔏 : Cast (𝔏 ^ (suc (suc n))) 𝔏
  -- Cast.cast Cast:𝔏^n,𝔏 = merge



-- record ICategory (C : 𝒰 𝑖) (𝑖𝑖 : 𝔏 ^ 2) : 𝒰 (𝑖 ､ (𝑖𝑖 ⁺)) where

-- -- | 1. A type family [..] assigning to every pair of objects $a\ b : C$
-- --      a type of /(homo-)morphisms/ $\AF{Hom}\ a\ b$ between them.
--   field Hom : C -> C -> 𝒰 (𝑖𝑖 ⌄ 0)


-- getfst = _⌄E_


-- record ICategory (C : 𝒰 𝑖) (𝑖𝑖 : 𝔏 ^ 2) : 𝒰 (𝑖 ､ 𝑖) where -- (𝑖 ､ (⨆ 𝑖𝑖 ⁺)) where
--   field Hom : C -> C -> 𝒰 (getfst 𝑖𝑖 0)  -- (𝑖𝑖 ⌄ 0)



-- private
--   merge : Vec 𝔏 m -> 𝔏
--   merge [] = ℓ₀
--   merge (ℓ ∷ []) = ℓ
--   merge (l ∷ j ∷ ls) = l ⊔ merge (j ∷ ls)

-- instance
--   IMultiJoinable:VecLevel : IMultiJoinable (Vec 𝔏 m) 𝔏
--   IMultiJoinable.⨆ IMultiJoinable:VecLevel = merge

-- 𝒰 : ∀{A : 𝒰' ℓ} -> {{_ : Cast A (Vec 𝔏 (suc m))}} -> (v : A) -> 𝒰' (merge (cast v) ⁺)
-- 𝒰 v = 𝒰' (⨆ (cast v))

-- 𝒰₀ = 𝒰' ℓ₀
-- 𝒰₁ = 𝒰' ℓ₁
-- 𝒰₂ = 𝒰' ℓ₂



