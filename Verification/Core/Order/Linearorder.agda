
module Verification.Core.Order.Linearorder where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
-- open import Verification.Core.Type

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Everything

open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder

--------------------------------------------------------------------
-- == Linear order
-- mainly from https://ncatlab.org/nlab/show/linear+order

private
  ⊥ = 𝟘-𝒰

record Base< {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) (a b : A) : 𝒰 𝑗 where
  constructor incl
  field Proof : (R a b)

open Base< public

record isLinearorder 𝑘 (A : 𝒰 𝑖 :& isSetoid {𝑗}) : 𝒰 (𝑘 ⁺ ､ 𝑗 ､ 𝑖) where
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
Linearorder 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isSetoid {𝑖 ⌄ 1} :& isLinearorder (𝑖 ⌄ 2)

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
  private
    instance
      isTotal:Linear : isPreorder 𝑗 A
      isPreorder._≤_ isTotal:Linear a b = b ≮ a
      isPreorder.reflexive isTotal:Linear = irrefl-<
      isPreorder._⟡_ isTotal:Linear {a} {b} {c} (p) (q) = P
        where
            P : c < a -> ⊥
            P r with compare-< r b
            ... | left x = q x
            ... | just x = p x
      isPreorder.transp-≤ isTotal:Linear = {!!}

    instance
      isPartialorder:Linear : isPartialorder ′ ⟨ A ⟩ ′
      isPartialorder.antisym isPartialorder:Linear (p) (q) = connected-< q p

    instance
      isTotalorder⁻:Linear : isTotalorder⁻ ′ ⟨ A ⟩ ′
      isTotalorder⁻.total⁻ isTotalorder⁻:Linear _ _ p = (λ a<b -> p ((λ {b<a -> asym-< a<b b<a})))


--------------------------------------------------------------------
-- Totalorder as Linearorder
isLinearorder:Totalorder⁺ : (X : Totalorder⁺ 𝑖) -> isLinearorder _ ′ ⟨ X ⟩ ′
isLinearorder:Totalorder⁺ X = record
  { my< = λ a b → b ≰ a
  ; irrefl-< = λ (incl x) → x reflexive
  ; asym-< = λ {a} {b} a≰b b≰a -> let q = total⁺ a b
                                  in case-Trichotomy q of
                                  (λ (b≤a , _) → b≰a .Proof b≤a)
                                  (λ a∼b -> b≰a .Proof (by-∼-≤_ a∼b ) )
                                  (λ (a≤b , _) → a≰b .Proof a≤b)
  ; compare-< = lem-10
  ; connected-< = lem-20
  ; transp-< = lem-30
  }
  where
    _<'_ : ⟨ X ⟩ -> ⟨ X ⟩ -> 𝒰 _
    _<'_ x y = Base< (λ a b -> b ≰ a) x y

    lem-10 : ∀{a c : ⟨ X ⟩} -> a <' c -> ∀(b : ⟨ X ⟩) -> (a <' b) +-𝒰 (b <' c)
    lem-10 {a} {c} (incl c≰a) b with total⁺ a b | total⁺ b c
    ... | gt (b≤a , b≁a) | Y = right (incl λ c≤b → c≰a (c≤b ⟡ b≤a))
    ... | eq b∼a         | Y = right (incl λ c≤b → c≰a (c≤b ⟡ (by-∼-≤ (b∼a ⁻¹))))
    ... | lt (a≤b , a≁b) | _ = left (incl λ b≤a → a≁b (antisym a≤b b≤a))

    lem-20 : ∀{a b} -> ¬ (a <' b) -> ¬ (b <' a) -> a ∼ b
    lem-20 {a} {b} ¬a<b ¬b<a with total⁺ a b
    ... | lt (a≤b , a≁b) = 𝟘-rec (¬a<b (incl λ b≤a → a≁b (antisym a≤b b≤a)))
    ... | eq a∼b = a∼b
    ... | gt (b≤a , b≁a) = 𝟘-rec (¬b<a (incl λ a≤b → b≁a (antisym b≤a a≤b)))

    lem-30 : ∀{a0 a1 b0 b1} -> (a0 ∼ a1) -> (b0 ∼ b1) -> a0 <' b0 -> a1 <' b1
    lem-30 p q (incl a0<b0) = incl λ b1≤a1 → a0<b0 (transp-≤ (q ⁻¹) (p ⁻¹) b1≤a1)


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
  _ ⟨ x∼y ⟩-∼-< y<z = transp-< (x∼y ⁻¹) refl y<z
  -- x<y ∙-< y<z

  ⟨⟩-∼-<-syntax : (x : A) {y z : A} → x ∼ y → y < z → x < z
  ⟨⟩-∼-<-syntax = _⟨_⟩-∼-<_
  infixr 2 ⟨⟩-∼-<-syntax
  infixr 2 _⟨_⟩-∼-<_

  _⟨_⟩-<-∼_ : (x : A) {y : A} {z : A} → x < y → y ∼ z → x < z
  _ ⟨ x<y ⟩-<-∼ y∼z = transp-< refl y∼z x<y
  -- x<y ∙-< y<z

  ⟨⟩-<-∼-syntax : (x : A) {y z : A} → x < y → y ∼ z → x < z
  ⟨⟩-<-∼-syntax = _⟨_⟩-<-∼_
  infixr 2 ⟨⟩-<-∼-syntax
  infixr 2 _⟨_⟩-<-∼_


