

{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Order.Partialorder where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder
-- open import Verification.Core.Type


record IPartialorder (A : 𝒰 𝑖) : (𝒰 (𝑖 ⁺)) where
  field {{Impl}} : IPreorder A
        antisym-≤ : ∀{a b : A} -> (a ≤ b) -> (b ≤ a) -> a ≡ b
open IPartialorder {{...}} public

unquoteDecl Partialorder partialorder = #struct "PartOrd" (quote IPartialorder) "A" Partialorder partialorder


module _ {A B : 𝒰 𝑖} {{_ : IPartialorder A}} {{_ : IPartialorder B}} where

  antisym-≤-⊕ : ∀{a b : A +-𝒰 B} -> (a ≤-⊕ b) -> (b ≤-⊕ a) -> a ≡ b
  antisym-≤-⊕ (left-≤ p) (left-≤ q) = cong left (antisym-≤ p q)
  antisym-≤-⊕ (right-≤ p) (right-≤ q) = cong right (antisym-≤ p q)

  instance
    IPartialorder:+ : IPartialorder (A +-𝒰 B)
    IPartialorder.Impl IPartialorder:+ = IPreorder:+
    IPartialorder.antisym-≤ IPartialorder:+ p q = antisym-≤-⊕ p q

_⊕-Partialorder_ : Partialorder 𝑖 -> Partialorder 𝑖 -> Partialorder 𝑖
_⊕-Partialorder_ A B = partialorder (⟨ A ⟩ +-𝒰 ⟨ B ⟩)

Partialorder:ℕ : Partialorder ℓ₀
⟨ Partialorder:ℕ ⟩ = ℕ
IPartialorder.Impl (of Partialorder:ℕ) = it
IPartialorder.antisym-≤ (of Partialorder:ℕ) = antisym-≤-ℕ

instance IPartialorder:ℕ = #openstruct Partialorder:ℕ

instance
  INotation:DirectSum:Partialorder : INotation:DirectSum (Partialorder 𝑖)
  INotation:DirectSum._⊕_ INotation:DirectSum:Partialorder = _⊕-Partialorder_


instance
  IPartialorder:⊤ : IPartialorder (Lift {j = 𝑖} 𝟙-𝒰)
  IPartialorder.Impl IPartialorder:⊤ = IPreorder:⊤
  IPartialorder.antisym-≤ IPartialorder:⊤ {a = lift tt} {b = lift tt} _ _ = refl


