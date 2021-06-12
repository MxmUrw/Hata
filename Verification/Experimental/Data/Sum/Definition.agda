
module Verification.Experimental.Data.Sum.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Function.Injective
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.EpiMono
-- open import Verification.Core.Category.Instance.Type





module _ {A : 𝒰 ℓ} {B : 𝒰 ℓ'} where
  split-+-Str : (x : A +-𝒰 B) -> (∑ λ (a : A) -> x ≡-Str left a) +-𝒰 (∑ λ b -> x ≡-Str right b)
  split-+-Str (left x) = left (x , refl)
  split-+-Str (just x) = right (x , refl)

  split-+ : (x : A +-𝒰 B) -> (∑ λ (a : A) -> x ≡ left a) +-𝒰 (∑ λ b -> x ≡ right b)
  split-+ (left x) = left (x , refl)
  split-+ (just x) = right (x , refl)

  cancel-right : (b : B) -> (A +-𝒰 B) -> B
  cancel-right b (left x) = b
  cancel-right b (right x) = x

  cancel-left : (a : A) -> (A +-𝒰 B) -> A
  cancel-left a (left x) = x
  cancel-left a (right x) = a

  either : {C : 𝒰 𝑖} -> (A -> C) -> (B -> C) -> (A +-𝒰 B) -> C
  either f g (left x) = f x
  either f g (just x) = g x

  rec-+-𝒰 = either

_≢_ : ∀{A : 𝒰 ℓ} (a b : A) -> 𝒰 ℓ
a ≢ b = (a ≡ b) -> 𝟘-𝒰

module _ {A : 𝒰 ℓ} {B : 𝒰 ℓ'} where
  left≢right : ∀{a : A}{b : B} -> left a ≢ right b
  left≢right p = transport (cong f p) tt
    where f : A +-𝒰 B -> 𝒰₀
          f (left x) = 𝟙-𝒰
          f (right x) = 𝟘-𝒰

  right≢left : ∀{a : A}{b : B} -> right b ≢ left a
  right≢left = λ p -> left≢right (sym p)


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} {D : 𝒰 𝑙} where
  map-+-𝒰 : ∀(f : A -> B) (g : C -> D) -> (A +-𝒰 C) -> (B +-𝒰 D)
  map-+-𝒰 f g = either (λ x -> left (f x)) (λ y -> right (g y))

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  instance
    isInjective:left : isInjective (left {A = A} {B = B})
    isInjective.injective isInjective:left {a} {.a} refl-StrId = refl

  instance
    isInjective:right : isInjective (right {A = A} {B = B})
    isInjective.injective isInjective:right {a} {.a} refl-StrId = refl


module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} {D : 𝒰 𝑙} where
  instance
    isInjective:either : {f : A -> C} {g : B -> C} -> {{_ : isInjective f}} {{_ : isInjective g}} -> isInjective (map-+-𝒰 f g)
    isInjective.injective (isInjective:either {f} {g}) {left x} {left x₁} p = cong-Str left (injective (injective {{isInjective:left}} p))
    isInjective.injective (isInjective:either {f} {g}) {just x} {just x₁} p = cong-Str right (injective (injective {{isInjective:right}} p))

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
