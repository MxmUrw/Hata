
module Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Substitution where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

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

-- [Definition]
-- | Let [..] be a parametrization.
module _ (𝓅 : 𝒯⊔Param 𝑖) where

  -- |> Applying a substitution |σ : 𝒯⊔Subst 𝓅 Γ Δ| to terms
  --    is defined by mutual induction over the definition
  --    of |𝒯⊔Term| and |𝒯⊔Terms| (where the latter is actually the definition
  --    of dependent lists).
  mutual
    subst-𝒯⊔Terms : ∀{Γ Δ Ε} -> 𝒯⊔Subst 𝓅 Γ Δ -> 𝒯⊔Terms 𝓅 Ε Γ -> 𝒯⊔Terms 𝓅 Ε Δ
    subst-𝒯⊔Terms σ ◌-⧜ = ◌-⧜
    subst-𝒯⊔Terms σ (incl x) = incl (subst-𝒯⊔Term σ x)
    subst-𝒯⊔Terms σ (t ⋆-⧜ s) = subst-𝒯⊔Terms σ t ⋆-⧜ subst-𝒯⊔Terms σ s

    subst-𝒯⊔Term : ∀{Γ Δ τ} -> 𝒯⊔Subst 𝓅 Γ Δ -> 𝒯⊔Term 𝓅 Γ τ -> 𝒯⊔Term 𝓅 Δ τ
    subst-𝒯⊔Term σ (var x) = σ _ x
    subst-𝒯⊔Term σ (con c ts) = con c (subst-𝒯⊔Terms σ ts)
-- //

-- [Remark]
-- | Actually, |subst-𝒯⊔Terms| is just the application of |subst-𝒯⊔Term| inside
--   of a dependent list. Theoretically, we could use functoriality of dependent lists
--   to define |subst-𝒯⊔Terms = map (subst-𝒯⊔Term σ)|, but this is not allowed by
--   the termination checker of Agda. Solutions to this problem exist (such as sized types),
--   but in a situation like this it is easier to simply do the induction by hand.

-- //

-- [Lemma]
-- | The substitution extends to a function [....]
  private postulate
    compose : ∀{Γ Δ Ε} -> 𝒯⊔Terms 𝓅 Γ Δ -> 𝒯⊔Terms 𝓅 Δ Ε -> 𝒯⊔Terms 𝓅 Γ Ε
-- |> This defines a category structure where the objects are lists, and the morphisms
--    are substitutions between them.

-- //

-- [Lemma]
-- | This category has coproducts.

-- //







