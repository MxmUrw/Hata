
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)


open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type


-----------------------------------------
-- Ctx'

-- | Contexts do contain type schemes, but they
--   are not represented by a list of types
--   with individual quantification declarations,
--   but instead by two lists: The first defines the
--   bound variables for each type in the context,
--   the second list is the actual context, and
--   contains a type for each quantification,
--   using variables from that quantification,
--   and an additionally given list of free variables.

-- [Definition]
-- | A /context quantification/ is defined by the type family [..].
--   It is defined as [....]
ℒHMQuant : ♮ℕ -> 𝒰₀
ℒHMQuant k = List[ i ∈ k ]  (ℒHMTypes)
-- |> An element |Q : ℒHMQuant k| is |k|-sized list,
--    where the |i|-th entry is the list of bound
--    variables to be used by the |i|-th type scheme
--    in the context (which is yet to be defined).

-- #Notation/Rewrite# ℒHMQuant = Quant_{HM}

-- //

-- [Definition]
-- | Given a context quantification |Q| of size |k|, and a
--   set of variables |μs|, we define
--   the /context over Q with free variables μs/.
--   Such a context is an inhabitant of the type |ℒHMCtx Q μs| [],
--   which is defined by [....]
ℒHMCtx : ∀{k} -> (Q : ℒHMQuant k) -> ∀ μs -> 𝒰₀
ℒHMCtx Q μs = List²[ αs ∈ Q ] (ℒHMType ⟨ μs ⊔ αs ⟩)

-- #Notation/Rewrite# ℒHMCtx = Ctx_{HM}
-- #Notation/Rewrite# List² = List

-- //


-- And a quantification together with a context by [....]
-- ℒHMCtx : (k : ♮ℕ) -> (μs : ℒHMTypes) -> 𝒰₀
-- ℒHMCtx k μs = ∑ λ (q : ℒHMQuant k) -> ℒHMCtxFor q μs



