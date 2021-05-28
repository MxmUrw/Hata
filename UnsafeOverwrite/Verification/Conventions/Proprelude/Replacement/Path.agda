
module Verification.Conventions.Proprelude.Replacement.Path where

open import Verification.Conventions.Proprelude.CubicalConventions
open import Agda.Builtin.Bool public
-- open import Verification.Conventions.Proprelude.Replacement.Empty


private
  variable
    ℓ  : Level
    A  : Type ℓ

-- Negation
-- infix 3 ¬_

-- ¬_ : Type ℓ → Type ℓ
-- ¬ A = A → 𝟘-𝒰


-- overwrite the path type with something which compiles
module _ {𝑖} {A : Type 𝑖} where
  _≡_ : A -> A -> Type 𝑖
  _≡_ a b = Bool -> A

  infix 4 _≡_


PathP : ∀{𝑗} -> (B : Bool -> Type 𝑗) -> (B false) -> B true -> Type 𝑗
PathP B b0 b1 = (b : Bool) -> B b

I = Bool
i0 = false
i1 = true

refl-Path : ∀{𝑖} {A : Type 𝑖} {a : A} -> a ≡ a
refl-Path {a = a} = λ i -> a


sym-Path : ∀{𝑖} {A : Type 𝑖} {a b : A} -> a ≡ b -> b ≡ a
sym-Path {a = a} {b} p false = b
sym-Path {a = a} {b} p true = a

trans-Path : ∀{𝑖} {A : Type 𝑖} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans-Path {a = a} {b} p q false = a
trans-Path {a = a} {b} {c} p q true = c

postulate
  transport : ∀{𝑖} -> ∀{A B : Type 𝑖} -> (P : A ≡ B) -> (a : A) -> B
  transportRefl : ∀{𝑖} -> ∀{A : Type 𝑖} -> (x : A) → transport (refl-Path {a = A}) x ≡ x



