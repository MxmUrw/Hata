
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition

open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Unification

open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition


-----------------------------------------
-- Ctx'


-- [Definition]
-- | We define a context quantification by
ℒHMQuant : (k : ♮ℕ) -> 𝒰₀
ℒHMQuant k = List[ i ∈ k ]  (ℒHMTypes)

-- //

-- [Definition]
-- | We define a context for a quantification |q| by [....]
ℒHMCtx : ∀{k} -> (q : ℒHMQuant k) -> ∀ μs -> 𝒰₀
ℒHMCtx q μs = List²[ a ∈ q ] (ℒHMType ⟨ μs ⊔ a ⟩)
-- //


-- And a quantification together with a context by [....]
-- ℒHMCtx : (k : ♮ℕ) -> (μs : ℒHMTypes) -> 𝒰₀
-- ℒHMCtx k μs = ∑ λ (q : ℒHMQuant k) -> ℒHMCtxFor q μs



