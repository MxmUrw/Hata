
module Verification.Experimental.Order.Preorder where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition

--------------------------------------------------------------------
-- == Preorder

record ≤-Base {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a b : A) : 𝒰 𝑗 where
  constructor incl
  field ⟨_⟩ : (R a b)
open ≤-Base public

record isPreorder 𝑘 (A : 𝒰 𝑖 :& isSetoid 𝑗) : 𝒰 (𝑘 ⁺ ､ 𝑗 ､ 𝑖) where
  field _≤'_ : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘
  _≤_ : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘
  _≤_ = ≤-Base _≤'_

  field reflexive : {a : ⟨ A ⟩} -> a ≤ a
        _⟡_ : {a b c : ⟨ A ⟩} -> a ≤ b -> b ≤ c -> a ≤ c
        transp-≤ : ∀{a₀ a₁ b₀ b₁ : ⟨ A ⟩} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ≤ b₀ -> a₁ ≤ b₁
  infixl 40 _≤_
  infixl 40 _⟡_

open isPreorder {{...}} public

Preorder : ∀ (𝑖 : 𝔏 ^ 3) -> 𝒰 (𝑖 ⁺)
Preorder 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isSetoid (𝑖 ⌄ 1) :& isPreorder (𝑖 ⌄ 2)

module _ {𝑖 : 𝔏 ^ 3} {A : 𝒰 _} {{_ : Preorder 𝑖 on A}} where
  _≰_ : A -> A -> 𝒰 _
  a ≰ b = ¬ a ≤ b

--------------------------------------------------------------------
-- == Partial order

module _ {𝑖 : 𝔏 ^ 3} where
  record isPartialorder (A : Preorder 𝑖) : 𝒰 𝑖 where
   field antisym : ∀{a b : ⟨ A ⟩} -> (a ≤ b) -> (b ≤ a) -> a ∼ b
open isPartialorder {{...}} public

Partialorder : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Partialorder 𝑖 = Preorder 𝑖 :& isPartialorder

----------------------------------------------------------
-- Derived instances

module _ {A : 𝒰 𝑖} {{_ : isSetoid 𝑗 A}} {{_ : isPreorder 𝑘 ′ A ′}} where
  instance
    isPreorder:Family : ∀{I : 𝒰 𝑙} -> isPreorder _ (′ (I -> A) ′)
    isPreorder._≤'_      isPreorder:Family f g = ∀{a} -> f a ≤' g a
    isPreorder.reflexive isPreorder:Family = incl ⟨ reflexive ⟩
    isPreorder._⟡_       isPreorder:Family (incl f) (incl g) = incl (⟨ incl f ⟡ incl g ⟩)
    isPreorder.transp-≤  isPreorder:Family (incl p) (incl q) f = incl (⟨ transp-≤ (incl p) (incl q) (incl ⟨ f ⟩) ⟩)

module _ {A : 𝒰 𝑖} {{_ : isSetoid 𝑗 A}} {{_ : isPreorder 𝑘 ′ A ′}} {{_ : isPartialorder ′ A ′}} where
  instance
    isPartialorder:Family : ∀{I : 𝒰 𝑙} -> isPartialorder (′ (I -> A) ′)
    isPartialorder.antisym isPartialorder:Family (incl p) (incl q) = incl ⟨ antisym (incl p) (incl q) ⟩

----------------------------------------------------------
-- Category of preorders

record isMonotone (A : Preorder 𝑖) (B : Preorder 𝑗) (f : SetoidHom ′ ⟨ A ⟩ ′ ′ ⟨ B ⟩ ′) : 𝒰 (𝑖 ､ 𝑗) where
  field monotone : ∀{a b : ⟨ A ⟩} -> (a ≤ b) -> ⟨ f ⟩ a ≤ ⟨ f ⟩ b

-- record isMonotone {A : 𝒰 _} {B : 𝒰 _} {{_ : Preorder 𝑖 on A}} {{_ : Preorder 𝑗 on B}} (f : (A -> B) :& isSetoidHom) : 𝒰 (𝑖 ､ 𝑗) where
--   field monotone : ∀{a b : A} -> (a ≤ b) -> ⟨ f ⟩ a ≤ ⟨ f ⟩ b
open isMonotone {{...}} public

-- record isMonotone {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isPreorder A}} {{_ : isPreorder B}} (f : A -> B) : 𝒰 (𝑖 ､ 𝑗) where
--   field monotone : ∀{a b : A} -> (a ≤ b) -> f a ≤ f b

Monotone : (A : Preorder 𝑖) (B : Preorder 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
Monotone A B = _ :& isMonotone A B

module _ {A : Preorder 𝑖} {B : Preorder 𝑗} where
  instance
    isSetoid:Monotone : isSetoid _ (Monotone A B)
    isSetoid._∼'_ isSetoid:Monotone f g = ⟨ f ⟩ ∼' ⟨ g ⟩
    isSetoid.isEquivRel:∼ isSetoid:Monotone = {!!}

-- unquoteDecl Monotone makeMonotone = #struct "Monotone" (quote isMonotone) "f" Monotone makeMonotone

{-
Category:Preorder : (𝑖 : 𝔏) -> Category _
⟨ Category:Preorder 𝑖 ⟩ = Preorder 𝑖
ICategory.Hom (of Category:Preorder 𝑖) = Monotone
ICategory._≣_ (of Category:Preorder 𝑖) f g = El f ≡ El g
ICategory.IEquiv:≣ (of Category:Preorder 𝑖) = {!!}
ICategory.id (of Category:Preorder 𝑖) = {!!}
ICategory._◆_ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-l-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-r-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.unit-2-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.assoc-l-◆ (of Category:Preorder 𝑖) = {!!}
ICategory.assoc-r-◆ (of Category:Preorder 𝑖) = {!!}
ICategory._◈_ (of Category:Preorder 𝑖) = {!!}
-}







{-
  record _<_ (a b : A) : 𝒰 𝑖 where
    constructor _,_
    field π-≤ : a ≤ b
    field π-≁ : ¬ a ∼ b

  open _<_ public
-}
  -- a < b = a ≤ b ×-𝒰 (a ∼ b -> 𝟘-𝒰)



module _ {𝑗 : 𝔏 ^ 3} {A : 𝒰 _} {{_ : Preorder 𝑗 on A}} where
  by-∼-≤_ : {a b : A} -> (a ∼ b) -> a ≤ b
  by-∼-≤_ p = transp-≤ refl p reflexive

  infixl 10 by-∼-≤_

  _⟨_⟩-≤_ : (x : A) {y : A} {z : A} → x ≤ y → y ≤ z → x ≤ z
  _ ⟨ x≤y ⟩-≤ y≤z = x≤y ⟡ y≤z

  ⟨⟩-≤-syntax : (x : A) {y z : A} → x ≤ y → y ≤ z → x ≤ z
  ⟨⟩-≤-syntax = _⟨_⟩-≤_
  infixr 2 ⟨⟩-≤-syntax
  infix  3 _∎-≤
  infixr 2 _⟨_⟩-≤_

  _∎-≤ : (x : A) → x ≤ x
  _ ∎-≤ = reflexive

  _⟨_⟩-∼-≤_ : (x : A) {y : A} {z : A} → x ∼ y → y ≤ z → x ≤ z
  _ ⟨ x≤y ⟩-∼-≤ y≤z = {!!} -- x≤y ⟡ y≤z

  ⟨⟩-∼-≤-syntax : (x : A) {y z : A} → x ∼ y → y ≤ z → x ≤ z
  ⟨⟩-∼-≤-syntax = _⟨_⟩-∼-≤_
  infixr 2 ⟨⟩-∼-≤-syntax
  infixr 2 _⟨_⟩-∼-≤_

  _⟨_⟩-≤-∼_ : (x : A) {y : A} {z : A} → x ≤ y → y ∼ z → x ≤ z
  _ ⟨ x≤y ⟩-≤-∼ y≤z = {!!} -- x≤y ⟡ y≤z

  ⟨⟩-≤-∼-syntax : (x : A) {y z : A} → x ≤ y → y ∼ z → x ≤ z
  ⟨⟩-≤-∼-syntax = _⟨_⟩-≤-∼_
  infixr 2 ⟨⟩-≤-∼-syntax
  infixr 2 _⟨_⟩-≤-∼_

{-

-}








{-
  _⟨_⟩-≤_ : (x : A) {y : A} {z : A} → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ x≤y ⟩ y≤z = x≤y ⟡ y≤z

  ≤⟨⟩-syntax : (x : A) {y z : A} → x ≤ y → y ≤ z → x ≤ z
  ≤⟨⟩-syntax = _⟨_⟩-≤_
  infixr 2 ≤⟨⟩-syntax
  infix  3 _∎-≤
  infixr 2 _⟨_⟩-≤_

  _∎-≤ : (x : A) → x ≤ x
  _ ∎-≤ = reflexive

  _⟨_⟩-∼-≤_ : (x : A) {y : A} {z : A} → x ∼ y → y ≤ z → x ≤ z
  _ ∼⟨ x≤y ⟩≤ y≤z = {!!} -- x≤y ⟡ y≤z

  ⟨⟩-∼-≤-syntax : (x : A) {y z : A} → x ∼ y → y ≤ z → x ≤ z
  ⟨⟩-∼-≤-syntax = _⟨_⟩-∼-≤_
  infixr 2 ⟨⟩-∼-≤-syntax
  infixr 2 _⟨_⟩-∼-≤_

  _⟨_⟩-≤-∼_ : (x : A) {y : A} {z : A} → x ≤ y → y ∼ z → x ≤ z
  _ ≤⟨ x≤y ⟩∼ y≤z = {!!} -- x≤y ⟡ y≤z

  ⟨⟩-≤-∼-syntax : (x : A) {y z : A} → x ≤ y → y ∼ z → x ≤ z
  ⟨⟩-≤-∼-syntax = _⟨_⟩-≤-∼_
  infixr 2 ⟨⟩-≤-∼-syntax
  infixr 2 _⟨_⟩-≤-∼_
-}




  -- _∼⟨_⟩-≤_ : (x : A) {y : A} {z : A} → x ∼ y → y ≤ z → x ≤ z
  -- _ ∼≤⟨ x≤y ⟩ y≤z = {!!} -- x≤y ⟡ y≤z

  -- ∼≤⟨⟩-syntax : (x : A) {y z : A} → x ∼ y → y ≤ z → x ≤ z
  -- ∼≤⟨⟩-syntax = _∼⟨_⟩-≤_
  -- infixr 2 ∼≤⟨⟩-syntax
  -- -- infix  3 _∎-≤
  -- infixr 2 _∼⟨_⟩-≤_



{-
{-
unquoteDecl Preorder preorder = #struct "PreOrd" (quote isPreorder) "A" Preorder preorder

-}


-}
{-
module _ {A : 𝒰 𝑖} {{_ : isPreorder A}} where
  infix 30 _<_
  _<_ : A -> A -> 𝒰 𝑖
  a < b = (a ≤ b) ×-𝒰 (a ≡ b -> 𝟘-𝒰)

  instance
    Cast:≡→≤ : ∀{a b : A} -> Cast (a ≡ b) IAnything (a ≤ b)
    Cast.cast (Cast:≡→≤ {a = a} {b}) e = transport (λ i -> e (~ i) ≤ b) reflexive


-- record isPreorderHom {A B : Preorder} (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰₀ where

-- record PreorderHom (A B : Preorder) : 𝒰₀ where

instance
  -- ICategory:Preorder : ICategory Preorder (𝑖 , 𝑖 ,-)
  -- ICategory:Preorder = {!!}
{-
  ICategory.Hom ICategory:Preorder = PreorderHom
  ICategory.id ICategory:Preorder = {!!}
  ICategory._◆_ ICategory:Preorder = {!!}
-}

  isPreorder:ℕ : isPreorder ℕ
  isPreorder._≤_ isPreorder:ℕ = _≤-ℕ_
  isPreorder.reflexive isPreorder:ℕ = reflexive-ℕ
  isPreorder.trans-≤ isPreorder:ℕ = trans-≤-ℕ




--------------------------------------------------------------------
-- == Concatenation of preorders

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑖} {{_ : isPreorder A}} {{_ : isPreorder B}} where

  data _≤-⊕_ : (a b : A +-𝒰 B) -> 𝒰 𝑖 where
    left-≤ : ∀{a b : A} -> a ≤ b -> left a ≤-⊕ left b
    right-≤ : ∀{a b : B} -> a ≤ b -> right a ≤-⊕ right b
    left-right-≤ : ∀{a : A} {b : B} -> left a ≤-⊕ right b


  trans-≤-⊕ : ∀{a b c} -> (a ≤-⊕ b) -> (b ≤-⊕ c) -> a ≤-⊕ c
  trans-≤-⊕ (left-≤ p) (left-≤ q) = left-≤ (trans-≤ p q)
  trans-≤-⊕ (left-≤ x) left-right-≤ = left-right-≤
  trans-≤-⊕ (right-≤ p) (right-≤ q) = right-≤ (trans-≤ p q)
  trans-≤-⊕ left-right-≤ (right-≤ x) = left-right-≤

  reflexive-⊕ : ∀{a} -> (a ≤-⊕ a)
  reflexive-⊕ {left x} = left-≤ reflexive
  reflexive-⊕ {just x} = right-≤ reflexive


  instance
    isPreorder:+ : isPreorder (A +-𝒰 B)
    isPreorder._≤_ isPreorder:+ = _≤-⊕_
    isPreorder.reflexive isPreorder:+ {a = a} = reflexive-⊕ {a}
    isPreorder.trans-≤ isPreorder:+ {a = a} = trans-≤-⊕ {a = a}


_⊕-Preorder_ : Preorder 𝑖 -> Preorder 𝑖 -> Preorder 𝑖
A ⊕-Preorder B = preorder (⟨ A ⟩ +-𝒰 ⟨ B ⟩)

instance
  INotation:DirectSum:Preorder : INotation:DirectSum (Preorder 𝑖)
  INotation:DirectSum._⊕_ INotation:DirectSum:Preorder = _⊕-Preorder_


--------------------------------------------------------------------
-- == Example instances

instance
  isPreorder:⊤ : ∀{𝑖} -> isPreorder (Lift {j = 𝑖} 𝟙-𝒰)
  isPreorder._≤_ isPreorder:⊤ a b = `𝟙`
  isPreorder.reflexive isPreorder:⊤ = lift tt
  isPreorder.trans-≤ isPreorder:⊤ a b = lift tt

-}
