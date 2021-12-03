
module Verification.Core.Data.Language.HindleyMilner.Variant.Typed.Definition where

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


data TypedℒHMᵈ (X : ⋆List Text -> 𝒰₀) : (Γ : ⋆List Text) -> 𝒰₀ where
  var  : ∀{i Γ} -> Γ ∍ i -> TypedℒHMᵈ X Γ
  hole : ∀{Γ} -> X Γ -> TypedℒHMᵈ X Γ
  slet : ∀{Γ} -> (name : Text) -> TypedℒHMᵈ X Γ -> TypedℒHMᵈ X (Γ ⋆ incl name) -> TypedℒHMᵈ X Γ
  -- sletₓ : ∀{Γ} -> TypedℒHMᵈ X Γ -> TypedℒHMᵈ X Γ -> TypedℒHMᵈ X Γ
  app : ∀{Γ} -> TypedℒHMᵈ X Γ -> TypedℒHMᵈ X Γ -> TypedℒHMᵈ X Γ
  lam : ∀{Γ} -> (name : Text) -> TypedℒHMᵈ X (Γ ⋆ incl name) -> TypedℒHMᵈ X Γ
  -- lamₓ : ∀{Γ} -> TypedℒHMᵈ X Γ -> TypedℒHMᵈ X Γ

-- data ℒHMType : 𝒰₀ where

TypedℒHMᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
TypedℒHMᵘ A = indexed (TypedℒHMᵈ (ix A))

macro TypedℒHM = #structureOn TypedℒHMᵘ
