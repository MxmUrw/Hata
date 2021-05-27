
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Order.Preorder where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type

--------------------------------------------------------------------
-- == Preorder

record IPreorder (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field _≤_ : A -> A -> 𝒰 𝑖
        refl-≤ : {a : A} -> a ≤ a
        trans-≤ : {a b c : A} -> a ≤ b -> b ≤ c -> a ≤ c
open IPreorder {{...}} public

unquoteDecl Preorder preorder = #struct "PreOrd" (quote IPreorder) "A" Preorder preorder


module _ {A : 𝒰 𝑖} {{_ : IPreorder A}} where
  infix 30 _<_
  _<_ : A -> A -> 𝒰 𝑖
  a < b = (a ≤ b) ×-𝒰 (a ≡ b -> 𝟘-𝒰)

  instance
    Cast:≡→≤ : ∀{a b : A} -> Cast (a ≡ b) IAnything (a ≤ b)
    Cast.cast (Cast:≡→≤ {a = a} {b}) e = transport (λ i -> e (~ i) ≤ b) refl-≤


-- record IPreorderHom {A B : Preorder} (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰₀ where

-- record PreorderHom (A B : Preorder) : 𝒰₀ where

instance
  -- ICategory:Preorder : ICategory Preorder (𝑖 , 𝑖 ,-)
  -- ICategory:Preorder = {!!}
{-
  ICategory.Hom ICategory:Preorder = PreorderHom
  ICategory.id ICategory:Preorder = {!!}
  ICategory._◆_ ICategory:Preorder = {!!}
-}

  IPreorder:ℕ : IPreorder ℕ
  IPreorder._≤_ IPreorder:ℕ = _≤-ℕ_
  IPreorder.refl-≤ IPreorder:ℕ = refl-≤-ℕ
  IPreorder.trans-≤ IPreorder:ℕ = trans-≤-ℕ




--------------------------------------------------------------------
-- == Concatenation of preorders

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : IPreorder A}} {{_ : IPreorder B}} where

  data _≤-⊕_ : (a b : A +-𝒰 B) -> 𝒰 𝑖 where
    left-≤ : ∀{a b : A} -> a ≤ b -> left a ≤-⊕ left b
    right-≤ : ∀{a b : B} -> a ≤ b -> right a ≤-⊕ right b
    left-right-≤ : ∀{a : A} {b : B} -> left a ≤-⊕ right b


  trans-≤-⊕ : ∀{a b c} -> (a ≤-⊕ b) -> (b ≤-⊕ c) -> a ≤-⊕ c
  trans-≤-⊕ (left-≤ p) (left-≤ q) = left-≤ (trans-≤ p q)
  trans-≤-⊕ (left-≤ x) left-right-≤ = left-right-≤
  trans-≤-⊕ (right-≤ p) (right-≤ q) = right-≤ (trans-≤ p q)
  trans-≤-⊕ left-right-≤ (right-≤ x) = left-right-≤

  refl-≤-⊕ : ∀{a} -> (a ≤-⊕ a)
  refl-≤-⊕ {left x} = left-≤ refl-≤
  refl-≤-⊕ {just x} = right-≤ refl-≤


  instance
    IPreorder:+ : IPreorder (A +-𝒰 B)
    IPreorder._≤_ IPreorder:+ = _≤-⊕_
    IPreorder.refl-≤ IPreorder:+ {a = a} = refl-≤-⊕ {a}
    IPreorder.trans-≤ IPreorder:+ {a = a} = trans-≤-⊕ {a = a}


_⊕-Preorder_ : Preorder 𝑖 -> Preorder 𝑖 -> Preorder 𝑖
A ⊕-Preorder B = preorder (⟨ A ⟩ +-𝒰 ⟨ B ⟩)

instance
  INotation:DirectSum:Preorder : INotation:DirectSum (Preorder 𝑖)
  INotation:DirectSum._⊕_ INotation:DirectSum:Preorder = _⊕-Preorder_


--------------------------------------------------------------------
-- == Example instances

instance
  IPreorder:⊤ : ∀{𝑖} -> IPreorder (Lift {j = 𝑖} 𝟙-𝒰)
  IPreorder._≤_ IPreorder:⊤ a b = `𝟙`
  IPreorder.refl-≤ IPreorder:⊤ = lift tt
  IPreorder.trans-≤ IPreorder:⊤ a b = lift tt



