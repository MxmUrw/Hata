
module Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
-- open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param



-- [Definition]
-- | Let [..] be a parametrization.
module _ (𝓅 : 𝒯⊔Param 𝑖) where
  -- |> Then multisorted terms,
  data 𝒯⊔Term : ⋆List (Sort 𝓅) -> Sort 𝓅 -> 𝒰 𝑖 where
  -- |> are defined as an inductive data type with the following two constructors
  -- | - {} [..]
    var : ∀{τ Γ} -> Γ ∍ τ -> 𝒯⊔Term Γ τ
  -- | - {} [..]
    con : ∀{Γ αs α} -> Con 𝓅 αs α -> ⋆List[ τ ∈ ι αs ] (𝒯⊔Term Γ τ) -> 𝒯⊔Term Γ α

  -- |: Additionally we define a substitution of sorts in a context |Γ| by
  --    terms in a context |Δ| by [....]
  𝒯⊔Terms : ⋆List (Sort 𝓅) -> ⋆List (Sort 𝓅) -> 𝒰 𝑖
  𝒯⊔Terms Γ Δ = ⋆List[ τ ∈ Γ ] (𝒯⊔Term Δ τ)

  -- |: This is the same data, but now in terms of a function
  𝒯⊔Subst : ⋆List (Sort 𝓅) -> ⋆List (Sort 𝓅) -> 𝒰 𝑖
  𝒯⊔Subst Γ Δ = ∀ τ -> Γ ∍ τ -> 𝒯⊔Term Δ τ

-- #Notation/Rewrite# 𝒯⊔Term = Term_{𝒯⊔}
-- #Notation/Rewrite# 𝒯⊔Terms = Terms_{𝒯⊔}
-- //

