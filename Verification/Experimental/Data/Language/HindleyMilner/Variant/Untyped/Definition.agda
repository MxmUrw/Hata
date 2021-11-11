
module Verification.Experimental.Data.Language.HindleyMilner.Variant.Untyped.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Module
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

ProductTheoryData = 𝕋×.統.𝒜


data UntypedℒHM (X : 𝒰₀) : (Γ : 人ℕ) -> 𝒰₀ where
  var  : ∀{i Γ} -> Γ ∍ i -> UntypedℒHM X Γ
  hole : ∀{Γ} -> X -> UntypedℒHM X Γ
  slet : ∀{Γ} -> UntypedℒHM X Γ -> UntypedℒHM X (Γ ⋆ incl tt) -> UntypedℒHM X Γ
  app : ∀{Γ} -> UntypedℒHM X Γ -> UntypedℒHM X Γ -> UntypedℒHM X Γ
  lam : ∀{Γ} -> UntypedℒHM X (Γ ⋆ incl tt) -> UntypedℒHM X Γ


data ℒHMType : 𝒰₀ where









