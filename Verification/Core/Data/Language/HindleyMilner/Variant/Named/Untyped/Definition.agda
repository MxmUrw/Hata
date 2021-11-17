
module Verification.Core.Data.Language.HindleyMilner.Variant.Untyped.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Nat
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.Universe
open import Verification.Core.Data.AllOf.Substitution
open import Verification.Core.Data.Indexed.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

ProductTheoryData = 𝕋×.統.𝒜


data UntypedℒHMᵈ (X : 人List Text -> 𝒰₀) : (Γ : 人List Text) -> 𝒰₀ where
  var  : ∀{i Γ} -> Γ ∍ i -> UntypedℒHMᵈ X Γ
  hole : ∀{Γ} -> X Γ -> UntypedℒHMᵈ X Γ
  slet : ∀{Γ} -> (name : Text) -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X (Γ ⋆ incl name) -> UntypedℒHMᵈ X Γ
  -- sletₓ : ∀{Γ} -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ
  app : ∀{Γ} -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ
  lam : ∀{Γ} -> (name : Text) -> UntypedℒHMᵈ X (Γ ⋆ incl name) -> UntypedℒHMᵈ X Γ
  -- lamₓ : ∀{Γ} -> UntypedℒHMᵈ X Γ -> UntypedℒHMᵈ X Γ

-- data ℒHMType : 𝒰₀ where

UntypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
UntypedℒHMᵘ A = indexed (UntypedℒHMᵈ (ix A))

macro UntypedℒHM = #structureOn UntypedℒHMᵘ









