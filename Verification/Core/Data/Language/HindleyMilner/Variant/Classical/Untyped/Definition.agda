
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural
-- open import Verification.Core.Category.Std.AllOf.Collection.Basics
-- open import Verification.Core.Data.AllOf.Collection.Basics
-- open import Verification.Core.Data.AllOf.Collection.TermTools


-- [Definition]
-- | The untyped HM terms are defined as follows.
data UntypedℒHM : (Γ : ♮ℕ) -> 𝒰₀ where
  var  : ∀{Γ i} -> Γ ∍♮ i -> UntypedℒHM Γ
  slet : ∀{Γ} -> UntypedℒHM Γ -> UntypedℒHM (tt ∷ Γ) -> UntypedℒHM Γ
  app : ∀{Γ} -> UntypedℒHM Γ -> UntypedℒHM Γ -> UntypedℒHM Γ
  lam : ∀{Γ} -> UntypedℒHM (tt ∷ Γ) -> UntypedℒHM Γ

-- //







