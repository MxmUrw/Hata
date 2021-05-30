
module Verification.Experimental.Order.Linearorder where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Prop.Everything

open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Totalorder

--------------------------------------------------------------------
-- == Linear order
-- mainly from https://ncatlab.org/nlab/show/linear+order

private
  ⊥ = 𝟘-𝒰

record Base< {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a b : A) : 𝒰 𝑗 where
  constructor incl
  field Proof : (R a b)

record isLinearorder 𝑘 (A : 𝒰 𝑖 :& isSetoid 𝑗) : 𝒰 (𝑘 ⁺ ､ 𝑗 ､ 𝑖) where
  field my< : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘
  _<_ : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘
  _<_ = Base< my<

  _≮_ : ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 𝑘
  _≮_ a b = ¬ a < b

  field irrefl-< : {a : ⟨ A ⟩} -> a ≮ a
        asym-< : ∀{a b : ⟨ A ⟩} -> a < b -> b ≮ a
        compare-< : ∀{a c : ⟨ A ⟩} -> a < c -> (b : ⟨ A ⟩) -> (a < b) +-𝒰 (b < c)
        connected-< : ∀{a b : ⟨ A ⟩} -> a ≮ b -> b ≮ a -> a ∼ b
        transp-< : ∀{a₀ a₁ b₀ b₁ : ⟨ A ⟩} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ < b₀ -> a₁ < b₁

  infixl 40 _<_

open isLinearorder {{...}} public

Linearorder : ∀ (𝑖 : 𝔏 ^ 3) -> 𝒰 (𝑖 ⁺)
Linearorder 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isSetoid (𝑖 ⌄ 1) :& isLinearorder (𝑖 ⌄ 2)

record isUnbound {𝑖 : 𝔏 ^ 3} (L : Linearorder 𝑖) : 𝒰 𝑖 where
  field getLess     : (a : ⟨ L ⟩) -> ⦋ (λ x -> ∣ x < a ∣) ⦌
  field getGreater  : (a : ⟨ L ⟩) -> ⦋ (λ x -> ∣ a < x ∣) ⦌
open isUnbound {{...}} public

record isDense {𝑖 : 𝔏 ^ 3} (L : Linearorder 𝑖) : 𝒰 𝑖 where
  field between : {a b : ⟨ L ⟩} -> a < b -> ⦋ (λ x -> ∣ a < x ×-𝒰 x < b ∣) ⦌
open isDense {{...}} public

--------------------------------------------------------------------
-- as Totalorder⁻

module LinearAsTotal {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} {A : Setoid 𝑖} {{_ : isLinearorder 𝑗 A}} where
  instance
    isTotal:Linear : isPreorder 𝑗 A
    isPreorder._≤'_ isTotal:Linear a b = b ≮ a
    isPreorder.reflexive isTotal:Linear = incl irrefl-<
    isPreorder._⟡_ isTotal:Linear {a} {b} {c} (incl p) (incl q) = incl P
      where
          P : c < a -> ⊥
          P r with compare-< r b
          ... | left x = q x
          ... | just x = p x
    isPreorder.transp-≤ isTotal:Linear = {!!}

  instance
    isPartialorder:Linear : isPartialorder ′ ⟨ A ⟩ ′
    isPartialorder.antisym isPartialorder:Linear (incl p) (incl q) = connected-< q p

  instance
    isTotalorder⁻:Linear : isTotalorder⁻ ′ ⟨ A ⟩ ′
    isTotalorder⁻.total⁻ isTotalorder⁻:Linear p = incl (λ a<b -> p (incl (λ {b<a -> asym-< a<b b<a})))

--------------------------------------------------------------------
-- Syntax

module _ {𝑗 : 𝔏 ^ 3} {A : 𝒰 _} {{_ : Linearorder 𝑗 on A}} where
  -- by-∼-<_ : {a b : A} -> (a ∼ b) -> a < b
  -- by-∼-<_ p = {!!} -- transp-< refl p refl-<
  -- infixl 10 by-∼-<_
  by-<-≁ : ∀{a b : A} -> a < b -> ¬ a ∼ b
  by-<-≁ p q = irrefl-< (transp-< q refl p)

  _∙-<_ : {x : A} {y : A} {z : A} → x < y → y < z → x < z
  _∙-<_ {x} {y} {z} x<y y<z with compare-< x<y z
  ... | left x<z = x<z
  ... | just z<y = 𝟘-rec (asym-< y<z z<y)

  _⟨_⟩-<_ : (x : A) {y : A} {z : A} → x < y → y < z → x < z
  _ ⟨ x<y ⟩-< y<z = x<y ∙-< y<z

  ⟨⟩-<-syntax : (x : A) {y z : A} → x < y → y < z → x < z
  ⟨⟩-<-syntax = _⟨_⟩-<_
  infixr 2 ⟨⟩-<-syntax
  -- infix  3 _⟨_⟩-<-∎
  infixr 2 _⟨_⟩-<_

  -- _⟨_⟩-<-∎ : (x : A) -> → x < x
  -- _ ∎-< = refl-<

  _⟨_⟩-∼-<_ : (x : A) {y : A} {z : A} → x ∼ y → y < z → x < z
  _ ⟨ x<y ⟩-∼-< y<z = {!!} -- x<y ∙-< y<z

  ⟨⟩-∼-<-syntax : (x : A) {y z : A} → x ∼ y → y < z → x < z
  ⟨⟩-∼-<-syntax = _⟨_⟩-∼-<_
  infixr 2 ⟨⟩-∼-<-syntax
  infixr 2 _⟨_⟩-∼-<_

  _⟨_⟩-<-∼_ : (x : A) {y : A} {z : A} → x < y → y ∼ z → x < z
  _ ⟨ x<y ⟩-<-∼ y<z = {!!} -- x<y ∙-< y<z

  ⟨⟩-<-∼-syntax : (x : A) {y z : A} → x < y → y ∼ z → x < z
  ⟨⟩-<-∼-syntax = _⟨_⟩-<-∼_
  infixr 2 ⟨⟩-<-∼-syntax
  infixr 2 _⟨_⟩-<-∼_


