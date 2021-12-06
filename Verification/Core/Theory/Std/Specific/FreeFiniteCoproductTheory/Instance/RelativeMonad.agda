
module Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition

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
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

module _ {𝓅 : 𝒯⊔Param 𝑖} where
  repure-𝒯⊔term : ∀{a} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ 𝒯⊔term 𝓅 a
  repure-𝒯⊔term i x = var x

  mutual
    reext-𝒯⊔Terms : ∀{a b αs} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ 𝒯⊔term 𝓅 b -> 𝒯⊔Terms 𝓅 αs ⟨ a ⟩ ⟶ 𝒯⊔Terms 𝓅 αs ⟨ b ⟩
    reext-𝒯⊔Terms f ◌-⧜ = ◌-⧜
    reext-𝒯⊔Terms f (x ⋆-⧜ y) = reext-𝒯⊔Terms f x ⋆-⧜ reext-𝒯⊔Terms f y
    reext-𝒯⊔Terms f (incl x) = incl (reext-𝒯⊔term f _ x)

    reext-𝒯⊔term : ∀{a b} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ 𝒯⊔term 𝓅 b -> 𝒯⊔term 𝓅 a ⟶ 𝒯⊔term 𝓅 b
    reext-𝒯⊔term f i (var x) = f i x
    reext-𝒯⊔term f i (con c x) = con c (reext-𝒯⊔Terms f x)

  instance
    isRelativeMonad:𝒯⊔term : isRelativeMonad (𝑓𝑖𝑛 (Sort 𝓅)) (𝒯⊔term 𝓅)
    isRelativeMonad.repure isRelativeMonad:𝒯⊔term = repure-𝒯⊔term
    isRelativeMonad.reext isRelativeMonad:𝒯⊔term = reext-𝒯⊔term
    isRelativeMonad.reunit-l isRelativeMonad:𝒯⊔term = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:𝒯⊔term = {!!}
    isRelativeMonad.reassoc isRelativeMonad:𝒯⊔term = {!!}

