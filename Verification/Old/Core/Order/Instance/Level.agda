
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Order.Instance.Level where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Order.Lattice
open import Verification.Old.Core.Order.Partialorder
open import Verification.Old.Core.Order.Preorder


Preorder:𝔏 : Preorder ℓ₀
⟨ Preorder:𝔏 ⟩ = 𝔏
IPreorder._≤_ (of Preorder:𝔏) a b = (a ⊔ b) ≡ b
IPreorder.refl-≤ (of Preorder:𝔏) = refl
IPreorder.trans-≤ (of Preorder:𝔏) {a = a} {b} {c} p q =
  let P = transport (λ i -> p (~ i) ⊔ c ≡ c) q
      Q = transport (λ i -> a ⊔ q i ≡ c) P
  in Q

instance IPreorder:𝔏 = #openstruct Preorder:𝔏

Partialorder:𝔏 : Partialorder ℓ₀
⟨ Partialorder:𝔏 ⟩ = 𝔏
IPartialorder.Impl (of Partialorder:𝔏) = IPreorder:𝔏
IPartialorder.antisym-≤ (of Partialorder:𝔏) p q = sym q ∙ p

instance IPartialorder:𝔏 = #openstruct Partialorder:𝔏

instance
  has∨-Preorder:𝔏 : has∨-Preorder 𝔏
  has∨-Preorder._∨_ has∨-Preorder:𝔏 = _⊔_
  has∨-Preorder.ι₀-∨ has∨-Preorder:𝔏 = refl
  has∨-Preorder.ι₁-∨ has∨-Preorder:𝔏 = refl
  has∨-Preorder.[_,_]-∨ has∨-Preorder:𝔏 p q = {!!}

  has⊥-Preorder:𝔏 : has⊥-Preorder 𝔏
  has⊥-Preorder.⊥ has⊥-Preorder:𝔏 = ℓ₀
  has⊥-Preorder.initial-⊥ has⊥-Preorder:𝔏 _ = refl

-- JoinLattice:𝔏 : JoinLattice ℓ₀
-- ⟨ JoinLattice:𝔏 ⟩ = 𝔏
-- IJoinLattice.Impl (of JoinLattice:𝔏) = IPartialorder:𝔏
-- IJoinLattice._∨_ (of JoinLattice:𝔏) = λ a b -> a ⊔ b
-- IJoinLattice.ι₀-∨ (of JoinLattice:𝔏) = refl
-- IJoinLattice.ι₁-∨ (of JoinLattice:𝔏) = refl
-- IJoinLattice.⊥ (of JoinLattice:𝔏) = ℓ₀
-- IJoinLattice.initial-⊥ (of JoinLattice:𝔏) = refl

-- instance IJoinLattice:𝔏 = #openstruct JoinLattice:𝔏




