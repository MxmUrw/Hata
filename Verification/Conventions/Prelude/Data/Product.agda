

module Verification.Conventions.Prelude.Data.Product where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.String
open import Verification.Conventions.Prelude.Data.Maybe
open import Verification.Conventions.Prelude.Data.Nat
open import Verification.Conventions.Prelude.Data.Fin

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

-- instance
  -- Index-Notation:^-𝒰,ℕ,A : ∀{A : 𝒰 𝑖} -> ∀{n} -> Index-Notation (A ^ (suc n)) (∆ ℕ) (λ i -> i ≤-ℕ-Dec n) (∆ A)
  -- Index-Notation._⌄_ Index-Notation:^-𝒰,ℕ,A x i {{p}} = x ⌄E i


---------------------------------------------------------------
-- new ellipsis based indexing

record Ellipsis (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _⋯_
  field fstEllipsis : A
  field sndEllipsis : A
infix 200 _⋯_

open Ellipsis public

record GoodEllipsis (e : Ellipsis ℕ) (max : ℕ) : 𝒰₀ where
  instance constructor goodEllipsis
  field {{fstProp}} : fstEllipsis e ≤-ℕ-Dec sndEllipsis e
  field {{sndProp}} : sndEllipsis e ≤-ℕ-Dec max

private
  size : Ellipsis ℕ -> ℕ
  size (a ⋯ b) = b ∸ a


⌄Ellipsis : ∀{A : 𝒰 𝑖} -> ∀{n} -> (A ^ (suc n)) -> (e : Ellipsis ℕ) -> {{_ : GoodEllipsis e n}} -> (A ^ suc (size e))
⌄Ellipsis {n = zero} a (.zero ⋯ .zero) ⦃ goodEllipsis ⦃ zero ⦄ ⦃ zero ⦄ ⦄ = a
⌄Ellipsis {n = suc n} (a , _) (.zero ⋯ .zero) ⦃ goodEllipsis ⦃ zero ⦄ ⦃ zero ⦄ ⦄ = a
⌄Ellipsis (a , as) (.zero ⋯ (suc n)) ⦃ goodEllipsis ⦃ zero ⦄ ⦃ suc ⦄ ⦄ = a , ⌄Ellipsis as (0 ⋯ n)
⌄Ellipsis (a , as) ((suc m) ⋯ (suc n)) ⦃ goodEllipsis {{suc}} {{suc}} ⦄ = ⌄Ellipsis as (m ⋯ n)
-- {{goodEllipsis {{it}} {{Q}}}}

instance
  Index-Notation:TupleEllipsis : ∀{A : 𝒰 𝑖} -> ∀{n} -> Index-Notation (A ^ (suc n)) (const (Ellipsis ℕ)) (λ e -> GoodEllipsis e n) (λ (_ , e) -> A ^ suc (size e))
  Index-Notation._⌄_ Index-Notation:TupleEllipsis = ⌄Ellipsis


instance
  fromNatEllipsis : HasFromNat (Ellipsis ℕ)
  fromNatEllipsis = record { Constraint = const 𝟙-𝒰 ; fromNat = λ n → n ⋯ n }




