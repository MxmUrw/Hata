
module Verification.Core.Data.Sum.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Function.Injective
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.EpiMono
-- open import Verification.Core.Category.Instance.Type


macro
  _+_ : ∀{𝑖 𝑗 : 𝔏} {𝑘 𝑙 : 𝔏 ^ 2} -> (𝒰 𝑖) [ 𝑙 ]→ (𝒰 𝑗) [ 𝑘 ]→ SomeStructure
  _+_ = λstr A ↦ λstr B ↦ #structureOn (A +-𝒰 B)
  infixr 40 _+_

macro
  _+⧿ : ∀{𝑖 𝑗 : 𝔏} {𝑘 : 𝔏 ^ 2} -> (𝒰 𝑗) [ 𝑘 ]→ SomeStructure
  _+⧿ {𝑖 = 𝑖} = λstr A ↦ #structureOn (λ (B : 𝒰 𝑖) -> A +-𝒰 B)
  infix 40 _+⧿

private instance _ = isSetoid:byId
private instance _ = isSetoid:byPath

module _ {A : 𝒰' ℓ} {B : 𝒰' ℓ'} where
  split-+-Str : (x : A + B) -> (∑ λ (a : A) -> x ≡-Str left a) + (∑ λ b -> x ≡-Str right b)
  split-+-Str (left x) = left (x , refl)
  split-+-Str (just x) = right (x , refl)

  split-+ : (x : A + B) -> (∑ λ (a : A) -> x ≡ left a) + (∑ λ b -> x ≡ right b)
  split-+ (left x) = left (x , refl)
  split-+ (just x) = right (x , refl)

  cancel-right : (b : B) -> (A + B) -> B
  cancel-right b (left x) = b
  cancel-right b (right x) = x

  cancel-left : (a : A) -> (A + B) -> A
  cancel-left a (left x) = x
  cancel-left a (right x) = a

  either : {C : 𝒰' 𝑖} -> (A -> C) -> (B -> C) -> (A +-𝒰 B) -> C
  either f g (left x) = f x
  either f g (just x) = g x

  rec-+ = either

_≢_ : ∀{A : 𝒰 ℓ} (a b : A) -> 𝒰 ℓ
a ≢ b = (a ≡ b) -> 𝟘-𝒰

module _ {A : 𝒰 ℓ} {B : 𝒰 ℓ'} where
  left≢right : ∀{a : A}{b : B} -> left a ≢ right b
  left≢right p = transport (cong f p) tt
    where f : A + B -> 𝒰₀
          f (left x) = 𝟙-𝒰
          f (right x) = 𝟘-𝒰

  right≢left : ∀{a : A}{b : B} -> right b ≢ left a
  right≢left = λ p -> left≢right (sym p)


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} {D : 𝒰 𝑙} where
  map-+ : ∀(f : A -> B) (g : C -> D) -> (A + C) -> (B + D)
  map-+ f g = either (λ x -> left (f x)) (λ y -> right (g y))

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
  mapLeft : ∀(f : A -> B) -> (A + C) -> (B + C)
  mapLeft f = either (λ x -> left (f x)) right

  mapRight : ∀(f : A -> B) -> (C + A) -> (C + B)
  mapRight f = either left (λ x -> right (f x))

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  instance
    isInjective:left : isInjective-𝒰 (left {A = A} {B = B})
    isInjective-𝒰.cancel-injective-𝒰 isInjective:left {a} {b} = {!!} -- refl-StrId = refl

  instance
    isInjective:right : isInjective-𝒰 (right {A = A} {B = B})
    isInjective-𝒰.cancel-injective-𝒰 isInjective:right {a} {b} = {!!} -- refl-StrId = refl


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} {D : 𝒰 𝑙} where
  instance
    isInjective-𝒰:either : {f : A -> C} {g : B -> C} -> {{_ : isInjective-𝒰 f}} {{_ : isInjective-𝒰 g}} -> isInjective-𝒰 (map-+ f g)
    isInjective-𝒰:either = {!!}


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  instance
    IShow:+-𝒰 : {{_ : IShow A}} {{_ : IShow B}} -> IShow (A + B)
    IShow:+-𝒰 = record { show = either show show }

    -- isInjective-𝒰.injective (isInjective-𝒰:either {f} {g}) {left x} {left x₁} p = cong-Str left (injective (injective {{isInjective-𝒰:left}} p))
    -- isInjective-𝒰.injective (isInjective-𝒰:either {f} {g}) {just x} {just x₁} p = cong-Str right (injective (injective {{isInjective-𝒰:right}} p))


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isSetoid {𝑖₁} A}} {{_ : isSetoid {𝑗₁} B}} where
  instance
    isSetoid:+ : isSetoid (A + B)
    isSetoid:+ = isSetoid:byDef
      (λ {(left a) (left b)  → Lift {𝑖₁ ､ 𝑗₁} {𝑖₁} (a ∼ b)
         ;(left a) (right b) → ⊥-𝒰
         ;(right a) (left b) → ⊥-𝒰
         ;(right a) (right b) → Lift {𝑖₁ ､ 𝑗₁} {𝑗₁} (a ∼ b)
         })
      (λ { {left a}  → ↥ refl
         ; {right a} → ↥ refl
         })
      {!!}
      {!!}


-- isSetoid:byDef (λ (a₀ , b₀) (a₁ , b₁) -> (a₀ ∼ a₁) × (b₀ ∼ b₁))
                 -- (refl , refl)
                 -- (λ (p , q) -> (p ⁻¹ , q ⁻¹))
                 -- (λ (p₀ , q₀) (p₁ , q₁) -> (p₀ ∙ p₁ , q₀ ∙ q₁))


{-
  isInjective:left : ∀{a b : A} -> left {B = B} a ≡ left b -> a ≡ b
  isInjective:left {a = a} p = cong (cancel-left a) p

  isInjective:right : ∀{a b : B} -> right {A = A} a ≡ right b -> a ≡ b
  isInjective:right {a = a} p = cong (cancel-right a) p

module _ {A B : 𝒰 ℓ} where
  instance
    IMono:left : IMono (left {A = A} {B = B})
    IMono.isMono IMono:left g h p = funExt (λ x -> isInjective:left (λ i -> p i x))

  instance
    IMono:right : IMono (right {A = A} {B = B})
    IMono.isMono IMono:right g h p = funExt (λ x -> isInjective:right (λ i -> p i x))
    -}
