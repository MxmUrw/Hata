
module Verification.Core.Data.List.Variant.FreeMonoid.Element.Properties where

open import Verification.Core.Conventions hiding (ℕ)


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Contradiction
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.FreeMonoid.Definition
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Setoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Monoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Element.Definition


module _ {A : 𝒰 𝑖} where

  module _ {a b : ⋆List A} {x : A} where

    instance
      isInjective-𝒰:left-∍ : isInjective-𝒰 (left-∍ {a = a} {b} {x})
      isInjective-𝒰.cancel-injective-𝒰 (isInjective-𝒰:left-∍) {m1} {m2} p = λ i -> f (p i) m1
        where f : (p : a ⋆ b ∍ x) -> a ∍ x -> a ∍ x
              f (left-∍ p) def = p
              f (right-∍ p) def = def

      isInjective-𝒰:right-∍ : isInjective-𝒰 (right-∍ {a = a} {b} {x})
      isInjective-𝒰:right-∍ = injective (λ {m1} {m2} p i → f (p i) m1)
        where f : (p : a ⋆ b ∍ x) -> b ∍ x -> b ∍ x
              f (left-∍ p) def = def
              f (right-∍ p) def = p

  instance
    isContradiction:left-∍≡right-∍ : ∀ {a b : ⋆List A} {x : A} {p : a ∍ x} -> {q : b ∍ x} -> isContradiction (left-∍ p ≡ right-∍ q)
    isContradiction:left-∍≡right-∍ {a} {b} {x} {p} {q} = contradiction (λ r → transport (cong P r) tt)
      where P : (a ⋆ b ∍ x) -> 𝒰₀
            P (left-∍ a) = ⊤-𝒰
            P (right-∍ a) = ⊥-𝒰

    isContradiction:right-∍≡left-∍ : ∀ {a b : ⋆List A} {x : A} {p : a ∍ x} -> {q : b ∍ x} -> isContradiction (right-∍ p ≡ left-∍ q)
    isContradiction:right-∍≡left-∍ = contradiction (λ x → contradict (λ i -> (x (~ i))))

  -- the element relation is discrete
  instance
    isDiscrete:∍ : ∀{as : ⋆List A} {a : A} -> isDiscrete (as ∍ a)
    isDiscrete._≟-Str_ (isDiscrete:∍ {as} {a}) = h
      where
        -- TODO prove this part with the additional fact that A is a set (needs to be added).
        g : ∀{a b} -> (p : a ≡ b) -> (x : incl b ∍ a) -> PathP (λ i -> incl (p i) ∍ a) incl x
        g p incl = {!!}

        f : ∀{as a} -> (x y : as ∍ a) -> Decision (x ≡ y)
        f incl y = yes (g refl-≡ y)
        f (right-∍ x) (right-∍ y) with f x y
        ... | yes p = yes (cong right-∍ p)
        ... | no ¬p = no (λ q -> ¬p (cancel-injective-𝒰 q))
        f (right-∍ x) (left-∍ y) = no impossible
        f (left-∍ x) (right-∍ y) = no impossible
        f (left-∍ x) (left-∍ y) with f x y
        ... | yes p = yes (cong left-∍ p)
        ... | no ¬p = no (λ q -> ¬p (cancel-injective-𝒰 q))

        h : ∀{as a} -> (x y : as ∍ a) -> Decision (x ≣ y)
        h x y with f x y
        ... | yes p = yes (≡→≡-Str p)
        ... | no ¬p = no (λ q -> ¬p (≡-Str→≡ q))
