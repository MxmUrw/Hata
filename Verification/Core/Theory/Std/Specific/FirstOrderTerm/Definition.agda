
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition where

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

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Param



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


-- [Hide]
-- | We also define |𝒯⊔term| as a function |𝐅𝐢𝐧𝐈𝐱 ⟶ 𝐈𝐱|.

  open import Verification.Core.Data.Indexed.Definition
  open import Verification.Core.Data.FiniteIndexed.Definition

  𝒯⊔termᵘ : (𝐅𝐢𝐧𝐈𝐱 (Sort 𝓅)) -> (𝐈𝐱 (Sort 𝓅) (𝐔𝐧𝐢𝐯 𝑖))
  𝒯⊔termᵘ Γ = indexed (λ τ → 𝒯⊔Term ⟨ Γ ⟩ τ)

  macro 𝒯⊔term = #structureOn 𝒯⊔termᵘ
-- //

