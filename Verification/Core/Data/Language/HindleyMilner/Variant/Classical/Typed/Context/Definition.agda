
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)


open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
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



