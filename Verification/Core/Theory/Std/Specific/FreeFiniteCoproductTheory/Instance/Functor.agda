
module Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Substitution

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

module _ {𝓅 : 𝒯⊔Param 𝑖} where
  mutual
    map-𝒯⊔Terms : ∀{αs} -> {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> (a ⟶ b) -> 𝒯⊔Terms 𝓅 αs ⟨ a ⟩ ⟶ 𝒯⊔Terms 𝓅 αs ⟨ b ⟩
    map-𝒯⊔Terms f ◌-⧜ = ◌-⧜
    map-𝒯⊔Terms f (x ⋆-⧜ y) = map-𝒯⊔Terms f x ⋆-⧜ map-𝒯⊔Terms f y
    map-𝒯⊔Terms f (incl x) = incl (map-𝒯⊔Term f _ x)

    map-𝒯⊔Term : {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> (a ⟶ b) -> 𝒯⊔term 𝓅 a ⟶ 𝒯⊔term 𝓅 b
    map-𝒯⊔Term f τ (var x) = var (⟨ f ⟩ τ x)
    map-𝒯⊔Term f τ (con c ts) = con c (map-𝒯⊔Terms f ts)

  -- [Hide]
  -- | The |map-𝒯⊔Term| function is a setoid hom.
  private
    mutual
      lem-1s : ∀{αs} -> ∀{a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> {f g : a ⟶ b} -> f ∼ g -> map-𝒯⊔Terms {αs} f ≡ map-𝒯⊔Terms {αs} g
      lem-1s p i ◌-⧜ = ◌-⧜
      lem-1s p i (incl x) = incl (lem-1 p _ i x)
      lem-1s p i (x ⋆-⧜ y) = (lem-1s p i x) ⋆-⧜ (lem-1s p i y)

      lem-1 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> {f g : a ⟶ b} -> f ∼ g -> map-𝒯⊔Term f ∼ map-𝒯⊔Term g
      lem-1 p τ i (var x) = var ((⟨ p ⟩ τ i) x)
      lem-1 p τ i (con c ts) = con c (lem-1s p i ts)

  instance
    isSetoidHom:map-𝒯⊔Term : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> isSetoidHom (a ⟶ b) (𝒯⊔term 𝓅 a ⟶ 𝒯⊔term 𝓅 b) map-𝒯⊔Term
    isSetoidHom:map-𝒯⊔Term = record { cong-∼ = lem-1 }
  -- //

  -- [Hide]
  -- | The |map-𝒯⊔Term| respects the categorical structures.
  private

    -- | It respects the identity.
    mutual
      lem-2s : ∀{αs} -> ∀{a : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> map-𝒯⊔Terms {αs} {a = a} id ≡ id-𝒰
      lem-2s i ◌-⧜ = ◌-⧜
      lem-2s i (incl x) = incl (lem-2 _ i x)
      lem-2s i (x ⋆-⧜ y) = lem-2s i x ⋆-⧜ lem-2s i y

      lem-2 : ∀{a : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} -> map-𝒯⊔Term {a = a} id ∼ id
      lem-2 τ i (var x) = var x
      lem-2 τ i (con x ts) = con x (lem-2s i ts)

    -- | It respects composition.
    module _ {a b c : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)} {f : a ⟶ b} {g : b ⟶ c} where
      mutual
        lem-3s : ∀{αs} -> map-𝒯⊔Terms {αs} (f ◆ g) ≡ map-𝒯⊔Terms f ◆ map-𝒯⊔Terms g
        lem-3s i ◌-⧜ = ◌-⧜
        lem-3s i (incl x) = incl (lem-3 _ i x)
        lem-3s i (x ⋆-⧜ y) = lem-3s i x ⋆-⧜ lem-3s i y

        lem-3 : map-𝒯⊔Term (f ◆ g) ∼ map-𝒯⊔Term f ◆ map-𝒯⊔Term g
        lem-3 τ i (var x) = var (⟨ g ⟩ τ (⟨ f ⟩ τ x))
        lem-3 τ i (con x ts) = con x (lem-3s i ts)
  -- //

  -- [Lemma]
  -- | The function |𝒯⊔term| is a functor.
  instance
    isFunctor:𝒯⊔Term : isFunctor (𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)) (𝐈𝐱 (Sort 𝓅) (𝐔𝐧𝐢𝐯 𝑖)) (𝒯⊔term 𝓅)
    isFunctor.map isFunctor:𝒯⊔Term = map-𝒯⊔Term
    isFunctor.isSetoidHom:map isFunctor:𝒯⊔Term = isSetoidHom:map-𝒯⊔Term
    isFunctor.functoriality-id isFunctor:𝒯⊔Term = lem-2
    isFunctor.functoriality-◆ isFunctor:𝒯⊔Term = lem-3

  -- //


