
module Verification.Core.Data.Language.HindleyMilner.Variant.Untyped.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

ProductTheoryData = 𝕋×.統.𝒜


data UntypedℒHM (X : 𝒰₀) : (Γ : 人ℕ) -> 𝒰₀ where
  var  : ∀{i Γ} -> Γ ∍ i -> UntypedℒHM X Γ
  hole : ∀{Γ} -> X -> UntypedℒHM X Γ
  slet : ∀{Γ} -> UntypedℒHM X Γ -> UntypedℒHM X (Γ ⋆ incl tt) -> UntypedℒHM X Γ
  app : ∀{Γ} -> UntypedℒHM X Γ -> UntypedℒHM X Γ -> UntypedℒHM X Γ
  lam : ∀{Γ} -> UntypedℒHM X (Γ ⋆ incl tt) -> UntypedℒHM X Γ


data ℒHMType : 𝒰₀ where









