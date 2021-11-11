
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Order.Totalorder where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Order.Preorder
open import Verification.Old.Core.Order.Partialorder
open import Verification.Old.Core.Order.Lattice
open import Verification.Old.Core.Type
open import Verification.Old.Core.Type.Decidable

--------------------------------------------------------------------
-- == Definitions

record ITotalorder (A : 𝒰 𝑖) : (𝒰 (𝑖 ⁺)) where
  field {{Impl}} : IPartialorder A
        total-≤ : ∀{a b : A} -> (a ≤ b -> 𝟘-𝒰) -> (b ≤ a -> 𝟘-𝒰) -> 𝟘-𝒰
open ITotalorder {{...}} public

unquoteDecl Totalorder totalorder = #struct "TotOrd" (quote ITotalorder) "A" Totalorder totalorder

record IDec-Totalorder (A : 𝒰 𝑖) {{_ : ITotalorder A}} : 𝒰 (𝑖 ⁺) where
  field _≤-?_ : ∀(a b : A) -> Decision (a ≤ b)
        {{Impl3}} : ∀{a b : A} -> IDec (a ≡ b)

open IDec-Totalorder {{...}} public

-- record IDec-Totalorder (A : 𝒰 𝑖) : (𝒰 (𝑖 ⁺)) where
--   field {{Impl1}} : ITotalorder A
--         {{Impl2}} : ∀{a b : A} -> IDec (a ≤ b)
--         {{Impl3}} : ∀{a b : A} -> IDec (a ≡ b)
-- open IDec-Totalorder {{...}} public

-- unquoteDecl Totalorder⍮Dec totalorder⍮Dec = #struct "TotOrdDec" (quote IDec-Totalorder) "A" Totalorder⍮Dec totalorder⍮Dec


instance
  IDec:< : ∀{A : 𝒰 𝑖} {{_ : ITotalorder A}} {{_ : IDec-Totalorder A}} -> {a b : A} -> IDec (a < b)
  IDec.decide (IDec:< {a = a} {b = b}) with (a ≤-? b) | (a ≡ b) ？
  ... | no x | no y = no (λ (p , q) -> x p)
  ... | no x | yes y = no (λ (p , q) -> q y)
  ... | yes x | no y = yes (x , y)
  ... | yes x | yes y = no (λ (p , q) -> q y)

-- decide-yes : ∀{A : 𝒰 𝑖} -> {{_ : IDec A}} -> {a : A} -> {{_ : decide =!= right a}} -> A
-- decide-yes {a = a} = a

--------------------------------------------------------------------
-- == The concatenation of total orders

module _ {A B : 𝒰 𝑖} {{_ : ITotalorder A}} {{_ : ITotalorder B}} where

  total-≤-⊕ : ∀{a b : A +-𝒰 B} -> (a ≤ b -> 𝟘-𝒰) -> (b ≤ a -> 𝟘-𝒰) -> 𝟘-𝒰
  total-≤-⊕ {a = left a} {left b} p q = total-≤ (λ Z -> p (left-≤ Z)) (λ Z -> q (left-≤ Z))
  total-≤-⊕ {a = left x} {right x₁} p q = p (left-right-≤)
  total-≤-⊕ {a = right x} {left x₁} p q = q (left-right-≤)
  total-≤-⊕ {a = right x} {right x₁} p q = total-≤ (λ Z -> p (right-≤ Z)) (λ Z -> q (right-≤ Z))

  instance
    ITotalorder:+ : ITotalorder (A +-𝒰 B)
    ITotalorder.Impl ITotalorder:+ = IPartialorder:+
    ITotalorder.total-≤ ITotalorder:+ {a = a} = total-≤-⊕ {a = a}


_⊕-Totalorder_ : Totalorder 𝑖 -> Totalorder 𝑖 -> Totalorder 𝑖
_⊕-Totalorder_ A B = totalorder (⟨ A ⟩ +-𝒰 ⟨ B ⟩)


instance
  INotation:DirectSum:Totalorder : INotation:DirectSum (Totalorder 𝑖)
  INotation:DirectSum._⊕_ INotation:DirectSum:Totalorder = _⊕-Totalorder_

--------------------------------------------------------------------
-- == Concatenation inherits decidability
module _ {A B : 𝒰 𝑖} {{_ : ITotalorder A}} {{_ : ITotalorder B}}
                     {{_ : IDec-Totalorder A}} {{_ : IDec-Totalorder B}} where

  Impl2-⊕ : ∀{a b : A +-𝒰 B} -> IDec (a ≤-⊕ b)
  IDec.decide (Impl2-⊕ {a = left x} {left y}) with x ≤-? y
  ... | no P = no λ {(left-≤ q) → P q}
  ... | yes P = yes (left-≤ P)
  IDec.decide (Impl2-⊕ {a = left x} {right x₁}) = yes left-right-≤ -- right (lift tt)
  IDec.decide (Impl2-⊕ {a = right x} {left x₁}) = no (λ {()}) -- left lower
  IDec.decide (Impl2-⊕ {a = right x} {right y}) with x ≤-? y
  ... | no P = no λ {(right-≤ q) → P q}
  ... | yes P = yes (right-≤ P)

  -- IDec.decide (Impl2-⊕ {a = left x} {left y}) = x ≤ y ？
  -- IDec.decide (Impl2-⊕ {a = left x} {right x₁}) = ? -- right (lift tt)
  -- IDec.decide (Impl2-⊕ {a = right x} {left x₁}) = ? -- left lower
  -- IDec.decide (Impl2-⊕ {a = right x} {right y}) = x ≤ y ？

  Impl3-⊕ : ∀{a b : A +-𝒰 B} -> IDec (a ≡ b)
  IDec.decide (Impl3-⊕ {a = left x} {left y}) = inside left ((x ≡ y) ？)
  IDec.decide (Impl3-⊕ {a = left x} {right x₁}) = no (left≢right)
  IDec.decide (Impl3-⊕ {a = right x} {left x₁}) = no (right≢left)
  IDec.decide (Impl3-⊕ {a = right x} {right y}) = inside right ((x ≡ y) ？)

  instance
    IDec-Totalorder:+ : IDec-Totalorder (A +-𝒰 B)
    -- IDec-Totalorder.Impl1 IDec-Totalorder:+ = ITotalorder:+
    IDec-Totalorder:+ = {!!}
    -- IDec-Totalorder.Impl2 IDec-Totalorder:+ {a = a} = Impl2-⊕ {a = a}
    -- IDec-Totalorder.Impl3 IDec-Totalorder:+ = Impl3-⊕

-- _⊕-Totalorder⍮Dec_ : Totalorder⍮Dec 𝑖 -> Totalorder⍮Dec 𝑖 -> Totalorder⍮Dec 𝑖
-- _⊕-Totalorder⍮Dec_ A B = totalorder⍮Dec (⟨ A ⟩ +-𝒰 ⟨ B ⟩)


--------------------------------------------------------------------
-- == Example instance

instance
  ITotalorder:𝟙-𝒰 : ITotalorder (Lift {j = 𝑖} 𝟙-𝒰)
  ITotalorder.Impl ITotalorder:𝟙-𝒰 = IPartialorder:⊤
  ITotalorder.total-≤ ITotalorder:𝟙-𝒰 p q = p (lift tt)

instance
  IDec-Totalorder:𝟙-𝒰 : IDec-Totalorder (Lift {j = 𝑖} 𝟙-𝒰)
  -- IDec-Totalorder.Impl1 IDec-Totalorder:𝟙-𝒰 = ITotalorder:𝟙-𝒰
  IDec-Totalorder:𝟙-𝒰 = {!!}
  -- IDec.decide (IDec-Totalorder.Impl2 IDec-Totalorder:𝟙-𝒰) = yes (lift tt)
  -- IDec.decide (IDec-Totalorder.Impl3 IDec-Totalorder:𝟙-𝒰 {a = (lift tt)} {lift tt}) = yes refl

--------------------------------------------------------------------
-- == Computing minima

-- module _ {A : 𝒰 𝑖} {{_ : IPreorder A}} {B : 𝒰 𝑖} {{_ : IPreorder B}} where

Totalorder:ℕ : Totalorder ℓ₀
⟨ Totalorder:ℕ ⟩ = ℕ
ITotalorder.Impl (of Totalorder:ℕ) = it
ITotalorder.total-≤ (of Totalorder:ℕ) {a = a} {b} p q with a ≟-ℕ b
... | lt x = p (<-weaken x)
... | eq x = p (0 , x)
... | gt x = q (<-weaken x)

instance ITotalorder:ℕ = #openstruct Totalorder:ℕ

private
  decide-≡ : (a b : ℕ) -> Decision (a ≡ b)
  decide-≡ a b with a ≟-ℕ b
  ... | lt x = no (λ e -> <-asym x (` e ⁻¹ `))
  ... | eq x = yes x
  ... | gt x = no (λ e -> <-asym x ` e `)

  decide-≤ : (a b : ℕ) -> Decision (a ≤ b)
  decide-≤ a b with a ≟-ℕ b
  ... | lt x = yes (<-weaken x)
  ... | eq x = yes ` x `
  ... | gt x = no (λ p -> <-asym x p)

instance
  IDec-Totalorder:ℕ : IDec-Totalorder ℕ
  IDec-Totalorder._≤-?_ IDec-Totalorder:ℕ = decide-≤
  IDec.decide (IDec-Totalorder.Impl3 IDec-Totalorder:ℕ) = decide-≡ _ _
  -- IDec.decide (IDec-Totalorder.Impl2 IDec-Totalorder:ℕ) = decide-≤ _ _
  -- IDec.decide (IDec-Totalorder.Impl3 IDec-Totalorder:ℕ) = decide-≡ _ _

  has⊥-Preorder:ℕ : has⊥-Preorder ℕ
  has⊥-Preorder.⊥ has⊥-Preorder:ℕ = 0
  has⊥-Preorder.initial-⊥ has⊥-Preorder:ℕ a = zero-≤

instance
  has⊥:𝟙 : has⊥-Preorder (Lift {j = 𝑖} 𝟙-𝒰)
  has⊥-Preorder.⊥ has⊥:𝟙 = ↥ tt
  has⊥-Preorder.initial-⊥ has⊥:𝟙 a = ↥ tt

  has∨:𝟙 : has∨-Preorder (Lift {j = 𝑖} 𝟙-𝒰)
  has∨-Preorder._∨_ has∨:𝟙 _ _ = ↥ tt
  has∨-Preorder.ι₀-∨ has∨:𝟙 = ↥ tt
  has∨-Preorder.ι₁-∨ has∨:𝟙 = ↥ tt
  has∨-Preorder.[_,_]-∨ has∨:𝟙 _ _ = ↥ tt

-- module _ {A B : Preorder 𝑖} where
module _ {A : 𝒰 𝑖} {{_ : ITotalorder A}} {B : 𝒰 𝑖} {{_ : ITotalorder B}} where
  instance
    has⊥:⊕ : {{_ : has⊥-Preorder ` A `}} -> has⊥-Preorder (A +-𝒰 B)
    has⊥-Preorder.⊥ has⊥:⊕ = left ⊥
    has⊥-Preorder.initial-⊥ has⊥:⊕ (left x) = left-≤ (initial-⊥ _)
    has⊥-Preorder.initial-⊥ has⊥:⊕ (just x) = left-right-≤
    -- has⊥-Preorder.⊥ has⊥:⊕ = left ⊥
    -- has⊥-Preorder.initial-⊥ has⊥:⊕ (left x) = initial-⊥ x
    -- has⊥-Preorder.initial-⊥ has⊥:⊕ (just x) = ↥ tt

    -- has∨:⊕ : {{_ : has∨-Preorder ` A `}} {{_ : has∨-Preorder ` B `}} -> has∨-Preorder (A +-𝒰 B)
    -- (has∨:⊕ has∨-Preorder.∨ left a) (left b) = left (a ∨ b)
    -- (has∨:⊕ has∨-Preorder.∨ left a) (just b) = just b
    -- (has∨:⊕ has∨-Preorder.∨ just a) (left b) = just a
    -- (has∨:⊕ has∨-Preorder.∨ just a) (just b) = just (a ∨ b)
    -- has∨-Preorder.ι₀-∨ has∨:⊕ = {!!}
    -- has∨-Preorder.ι₁-∨ has∨:⊕ = {!!}

module _ {A : 𝒰 𝑖} {{_ : IPreorder A}} where
  ≡→≤ : ∀{a b : A} -> (a ≡ b) -> a ≤ b
  ≡→≤ {a = a} {b} p = transport (λ i -> p (~ i) ≤ b) refl-≤

module _ {A : 𝒰 𝑖} {{_ : ITotalorder A}} {{_ : IDec-Totalorder A}} where
  min : A -> A -> A
  min a b with a ≤-? b
  ... | no x = b
  ... | yes x = a


  max : A -> A -> A
  max a b with (a ≤-? b)
  ... | no x = a
  ... | yes x = b

  -- max' : (a b : A) -> ∑ λ x -> a ≤ x
  -- max' a b with a ≤ b ？
  -- ... | left x = a
  -- ... | right x = b

  ≤-switch : ∀{a b : A} -> (a ≤ b -> 𝟘-𝒰) -> b ≤ a
  ≤-switch p = {!!}



  ι₀-max : ∀{a b : A} -> a ≤ max a b
  ι₀-max {a} {b} with (((a ≤-? b)))
  ... | no x = {!!}
  ... | yes x = {!!}

  ι₁-max : ∀{a b : A} -> b ≤ max a b
  ι₁-max {a} {b} with (a ≤-? b)
  ... | no x = ≤-switch x
  ... | yes x = refl-≤

  sym-max : ∀{a b : A} -> max a b ≡ max b a
  sym-max {a} {b} with ((a ≤-? b)) | ((b ≤-? a))
  ... | no p | no q = antisym-≤ (≤-switch q) (≤-switch p)
  ... | no p | yes q = refl
  ... | yes p | no q = refl
  ... | yes p | yes q = antisym-≤ q p


  max-reduce-r : ∀{a b : A} -> a ≤ b -> max a b ≡ b
  max-reduce-r p = {!!}

  max-initial : ∀{a b c : A} -> (a ≤ c) -> (b ≤ c) -> (max a b ≤ c)
  max-initial = {!!}

  instance
    has∨:Dec-Totalorder : has∨-Preorder ` A `
    has∨-Preorder._∨_ has∨:Dec-Totalorder = max
    has∨-Preorder.ι₀-∨ has∨:Dec-Totalorder = ι₀-max
    has∨-Preorder.ι₁-∨ has∨:Dec-Totalorder = {!!}
    has∨-Preorder.[_,_]-∨ has∨:Dec-Totalorder = max-initial

