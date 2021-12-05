
module Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Substitution

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

module _ {𝒹 : 𝒯⊔Param 𝑖} where
  mutual
    -- map-𝒯⊔Terms : ∀{αs} -> {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝒹)} -> (a ⟶ b) -> 𝒯⊔Terms 𝒹 αs (incl a) ⟶ 𝒯⊔Terms 𝒹 αs (incl b)
    map-𝒯⊔Terms : ∀{αs} -> {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝒹)} -> (a ⟶ b) -> 𝒯⊔Terms 𝒹 αs {!!} ⟶ {!!}
    map-𝒯⊔Terms = {!!}
    -- (incl a) ⟶ 𝒯⊔Terms 𝒹 αs (incl b)
    -- map-𝒯⊔Terms = {!!}
    -- map-𝒯⊔Terms f ◌-⧜ = ◌-⧜
    -- map-𝒯⊔Terms f (x ⋆-⧜ y) = map-𝒯⊔Terms f x ⋆-⧜ map-𝒯⊔Terms f y
    -- map-𝒯⊔Terms f (incl x) = incl (map-𝒯⊔Term f _ x)

{-
    map-𝒯⊔Term : {a b : 𝐅𝐢𝐧𝐈𝐱 (Sort 𝒹)} -> (a ⟶ b) -> 𝒯⊔Term 𝒹 a ⟶ 𝒯⊔Term 𝒹 b
    map-𝒯⊔Term f τ (var x) = var (⟨ f ⟩ τ x)
    map-𝒯⊔Term f τ (con c x) = con c (map-𝒯⊔Terms f x)

  instance
    isFunctor:𝒯⊔Term : isFunctor (𝐅𝐢𝐧𝐈𝐱 (Sort 𝒹)) (𝐈𝐱 (Sort 𝒹) (𝐔𝐧𝐢𝐯 𝑖)) (𝒯⊔Term 𝒹)
    isFunctor.map isFunctor:𝒯⊔Term = map-𝒯⊔Term
    isFunctor.isSetoidHom:map isFunctor:𝒯⊔Term = {!!}
    isFunctor.functoriality-id isFunctor:𝒯⊔Term = {!!}
    isFunctor.functoriality-◆ isFunctor:𝒯⊔Term = {!!}
    -}
