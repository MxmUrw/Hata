
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
-- open import Verification.Core.Data.Indexed.Definition

-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
-- open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries



data UntypedℒHMᵈ : (Γ : ♮ℕ) -> 𝒰₀ where
  -- var  : ∀{i Γ} -> Γ ∍ i -> UntypedℒHMᵈ Γ
  var  : ∀{Γ i} -> Γ ∍♮ i -> UntypedℒHMᵈ Γ
  slet : ∀{Γ} -> UntypedℒHMᵈ Γ -> UntypedℒHMᵈ (tt ∷ Γ) -> UntypedℒHMᵈ Γ
  app : ∀{Γ} -> UntypedℒHMᵈ Γ -> UntypedℒHMᵈ Γ -> UntypedℒHMᵈ Γ
  lam : ∀{Γ} -> UntypedℒHMᵈ (tt ∷ Γ) -> UntypedℒHMᵈ Γ

UntypedℒHM = UntypedℒHMᵈ

-- UntypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
-- UntypedℒHMᵘ = indexed (UntypedℒHMᵈ)

-- macro UntypedℒHM = #structureOn UntypedℒHMᵘ











