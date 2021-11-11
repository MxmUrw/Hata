
module Verification.Old.Core.Type.Instance.Fin where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Order.Lattice
open import Verification.Old.Core.Order.Preorder
open import Verification.Old.Core.Order.Partialorder
open import Verification.Old.Core.Order.Totalorder
open import Verification.Old.Core.Order.Instance.Level

open import Verification.Old.Core.Type.Instance.Nat
open import Verification.Old.Core.Type.Decidable

-- data _≤-Fin_ : Fin m -> Fin n -> 𝒰 ℓ₀ where
--   refl-≤-Fin : ∀ {i : Fin n} -> i ≤-Fin i
--   suc-≤-Fin : ∀{i : Fin m} {j : Fin n} -> i ≤-Fin j -> i ≤-Fin (suc j)

data _≤-Fin_ : Fin m -> Fin n -> 𝒰 ℓ₀ where
  from-≤ : ∀{i j : ℕ} -> ∀{ip : i <-ℕ m} -> ∀{jp : j <-ℕ n} -> i ≤ j -> (i , ip) ≤-Fin (j , jp)


Preorder:Fin : ∀ n -> Preorder ⊥
⟨ Preorder:Fin n ⟩ = Fin n
IPreorder._≤_ (of Preorder:Fin n) = _≤-Fin_
IPreorder.refl-≤ (of Preorder:Fin n) = from-≤ refl-≤
IPreorder.trans-≤ (of Preorder:Fin n) (from-≤ p) (from-≤ q)= from-≤ (trans-≤ p q)

instance IPreorder:Fin = #openstruct Preorder:Fin



Partialorder:Fin : ∀ n -> Partialorder ⊥
⟨ Partialorder:Fin n ⟩ = Fin n
IPartialorder.Impl (of Partialorder:Fin n) = it
IPartialorder.antisym-≤ (of Partialorder:Fin n) {a = a} {b = b} (from-≤ p) (from-≤ q) =
  let P = antisym-≤ p q
  in toℕ-injective P

instance IPartialorder:Fin = #openstruct Partialorder:Fin

Totalorder:Fin : ∀ n -> Totalorder ⊥
⟨ Totalorder:Fin n ⟩ = Fin n
ITotalorder.Impl (of Totalorder:Fin n) = it
ITotalorder.total-≤ (of Totalorder:Fin n) p q = total-≤ (λ a -> p (from-≤ a)) (λ b -> q (from-≤ b))

instance ITotalorder:Fin = #openstruct Totalorder:Fin

syntax-as : ∀(A : 𝒰 𝑖) -> A -> A
syntax-as _ a = a

infixl 10 syntax-as
syntax syntax-as A a = a as A
-- _as_ : ∀{}

-- instance _ = IDec-Totalorder:ℕ

instance _ = IDec-Totalorder.Impl2 {{ITotalorder:ℕ}} IDec-Totalorder:ℕ
instance _ = IDec-Totalorder.Impl3 {{ITotalorder:ℕ}} IDec-Totalorder:ℕ

mytesta : (a b : ℕ) -> Decision (a ≤ b)
mytesta a b = decide

instance
  IDec-Totalorder:Fin : IDec-Totalorder (Fin n)
  IDec.decide (IDec-Totalorder.Impl2 IDec-Totalorder:Fin {a = a} {b}) with decide as Decision ((a .fst) ≤ (b .fst))
  ... | yes p = yes (from-≤ p)
  ... | no ¬p = no (λ {(from-≤ x) -> ¬p x})
  IDec.decide (IDec-Totalorder.Impl3 IDec-Totalorder:Fin {a = a} {b}) with decide as Decision (a .fst ≡ b .fst)
  ... | yes p = yes (toℕ-injective p)
  ... | no ¬p = no (λ e -> ¬p (cong fst e))


