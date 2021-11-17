
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
-- open import Verification.Core.Data.Indexed.Definition

-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries



data UntypedℒHMᵈ (X : 人ℕ -> 𝒰₀) : (Γ : 人ℕ) -> 𝒰₀ where
  var  : ∀{i Γ} -> Γ ∍ i -> UntypedℒHMᵈ X Γ
  hole : ∀{Γ} -> X Γ -> UntypedℒHMᵈ X Γ
  slet : ∀{Γ} -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X (Γ ⋆ incl tt) -> UntypedℒHMᵈ X Γ
  app : ∀{Γ} -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ
  lam : ∀{Γ} -> UntypedℒHMᵈ X (Γ ⋆ incl tt) -> UntypedℒHMᵈ X Γ


UntypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
UntypedℒHMᵘ A = indexed (UntypedℒHMᵈ (ix A))

macro UntypedℒHM = #structureOn UntypedℒHMᵘ











