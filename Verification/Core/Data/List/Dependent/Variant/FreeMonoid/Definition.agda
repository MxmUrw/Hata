
module Verification.Core.Data.List.Dependent.Variant.FreeMonoid.Definition where


open import Verification.Core.Conventions hiding (ℕ)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Function.Property
open import Verification.Core.Data.Prop.Definition
-- open import Verification.Core.Data.Nat.Definition
-- open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Definition
-- open import Verification.Core.Data.List.Variant.Base.Instance.Monoid
-- open import Verification.Core.Set.Contradiction
open import Verification.Core.Algebra.Monoid.Definition


module _ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) where
  infixl 29 _⋆-⧜_

  data ⋆Listᴰ : (as : ⋆List A) -> 𝒰 (𝑖 ､ 𝑗) where
    ◌-⧜ : ⋆Listᴰ (◌)
    incl : ∀{a} -> B a -> ⋆Listᴰ (incl a)
    _⋆-⧜_ : ∀{a b} -> ⋆Listᴰ a -> ⋆Listᴰ b -> ⋆Listᴰ (a ⋆ b)

  syntax ⋆Listᴰ (λ a -> B) as = ⋆List[ a ∈ as ] B

module _ {A : 𝒰 𝑖} (R : ⋆List A -> A -> 𝒰 𝑖) where
  CtxHom : ⋆List A -> ⋆List A -> 𝒰 _
  CtxHom as bs = ⋆List[ a ∈ as ] (R bs a)

  -- CtxHom as bs = ⋆Listᴰ (R bs) as


-- [Hide]
module _ {A : 𝒰 𝑖} {R : A -> 𝒰 𝑗} where

  instance
    isSetoid:⋆Listᴰ : ∀{a} -> isSetoid (⋆Listᴰ R a)
    isSetoid:⋆Listᴰ = isSetoid:byId

  construct-⋆Listᴰ : ∀{as : ⋆List A} -> (∀ a -> as ∍ a -> R a) -> ⋆Listᴰ R as
  construct-⋆Listᴰ {incl x} r = incl (r x incl)
  construct-⋆Listᴰ {as ⋆-⧜ as₁} r = construct-⋆Listᴰ (λ a x -> r a (left-∍ x)) ⋆-⧜ construct-⋆Listᴰ (λ a x -> r a (right-∍ x))
  construct-⋆Listᴰ {◌-⧜} r = ◌-⧜

  construct-CtxHom = construct-⋆Listᴰ


  destruct-⋆Listᴰ : ∀{as : ⋆List A} -> ⋆Listᴰ R as -> (∀ a -> as ∍ a -> R a)
  destruct-⋆Listᴰ (incl x) a incl = x
  destruct-⋆Listᴰ (f ⋆-⧜ g) a (left-∍ p) = destruct-⋆Listᴰ f a p
  destruct-⋆Listᴰ (f ⋆-⧜ g) a (right-∍ p) = destruct-⋆Listᴰ g a p

  destruct-CtxHom = destruct-⋆Listᴰ

  inv-l-◆-construct-⋆Listᴰ : ∀{as : ⋆List A} -> (r : ∀ a -> as ∍ a -> R a) -> destruct-⋆Listᴰ (construct-⋆Listᴰ r) ≡ r
  inv-l-◆-construct-⋆Listᴰ {incl x} r = λ {i a incl → r x incl}
  inv-l-◆-construct-⋆Listᴰ {as ⋆-⧜ as₁} r i a (right-∍ x) = inv-l-◆-construct-⋆Listᴰ (λ a -> r a ∘ right-∍) i a x
  inv-l-◆-construct-⋆Listᴰ {as ⋆-⧜ as₁} r i a (left-∍ x)  = inv-l-◆-construct-⋆Listᴰ (λ a -> r a ∘ left-∍)  i a x
  inv-l-◆-construct-⋆Listᴰ {◌-⧜} r i a ()

  inv-r-◆-construct-⋆Listᴰ : ∀{as : ⋆List A} -> (f : ⋆Listᴰ R as) -> construct-⋆Listᴰ (destruct-⋆Listᴰ f) ≡ f
  inv-r-◆-construct-⋆Listᴰ ◌-⧜ = refl-≡
  inv-r-◆-construct-⋆Listᴰ (incl x) = refl-≡
  inv-r-◆-construct-⋆Listᴰ (f ⋆-⧜ g) = λ i → inv-r-◆-construct-⋆Listᴰ f i ⋆-⧜ inv-r-◆-construct-⋆Listᴰ g i

  module _ {as : ⋆List A} where
    instance
      isIso:destruct-⋆Listᴰ : isIso {𝒞 = 𝐔𝐧𝐢𝐯 _} (hom (destruct-⋆Listᴰ {as = as}))
      isIso:destruct-⋆Listᴰ = record
        { inverse-◆ = construct-⋆Listᴰ
        ; inv-r-◆ = funExt inv-r-◆-construct-⋆Listᴰ
        ; inv-l-◆ = funExt inv-l-◆-construct-⋆Listᴰ
        }

    instance
      isInjective:destruct-⋆Listᴰ : isInjective-𝒰 (destruct-⋆Listᴰ {as = as})
      isInjective:destruct-⋆Listᴰ = isInjective-𝒰:byIso

  module §-⋆Listᴰ where
    prop-1 : ∀{as bs : ⋆List A} -> ∀{xs xs' : ⋆Listᴰ R as} {ys ys' : ⋆Listᴰ R bs} -> StrId {A = ⋆Listᴰ R (as ⋆ bs)} (xs ⋆-⧜ ys) (xs' ⋆-⧜ ys') -> (xs ≣ xs') ×-𝒰 (ys ≣ ys')
    prop-1 = {!!}

  incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a} -> R a -> ⋆Listᴰ R (incl a)
  incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 = incl

  cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a} -> {f g : R a} -> incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 f ≣ incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 g -> f ≣ g
  cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 refl-≣ = refl-≣
-- //


