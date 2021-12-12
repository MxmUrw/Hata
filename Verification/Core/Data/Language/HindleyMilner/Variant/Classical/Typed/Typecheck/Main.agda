
{-# OPTIONS --experimental-lossy-unification #-}

module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Main where

open import Verification.Conventions hiding (ℕ ; _⊔_)


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.Var
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.SLet
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.Lam
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.App



-- [Theorem]
-- | Typechecking for HM is decidable, the algorithm produces the
--   initial typing instance. That is, there is a function [....]
γ : ∀{μs k} {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) -> (te : UntypedℒHM k)
  -> (¬ CtxTypingInstance Γ te)
    +
     (InitialCtxTypingInstance Γ te)

-- | Proof.
γ {μs} {k} {Q} Γ (var k∍i) = right $ (_ , typecheck-Var.Result Γ k∍i)

γ {μs = νs} {Q = Q} Γ (slet te se) with γ Γ te
... | (left err) = left (typecheck-slet.Fail-te.Result Γ te se err)
... | (right 𝑇-te) with γ _ se
... | (left err) = left (typecheck-slet.Success-te.Fail-se.Result Γ te se 𝑇-te err)
... | (right 𝑇-se) = right (typecheck-slet.Success-te.Success-se.Result Γ te se 𝑇-te 𝑇-se)

γ {μs = νsₐ} Γ (app te se) with γ Γ te
... | (left err) = left (typecheck-app.Fail-te.Result Γ te se err)
... | (right 𝑇-te) with γ _ se
... | (left err) = left (typecheck-app.Success-te.Fail-se.Result Γ te se 𝑇-te err)
... | (right 𝑇-se) with unify-ℒHMTypes _ _
... | (left err) = left (typecheck-app.Success-te.Success-se.Fail-Coeq.Result Γ te se 𝑇-te 𝑇-se err)
... | (right x) = right (typecheck-app.Success-te.Success-se.Success-Coeq.Result Γ te se 𝑇-te 𝑇-se x)

γ {μs} {k} {Q = Q} Γ (lam te) with γ _ te
... | (left err) = left (typecheck-lam.Fail-te.Result Γ te err)
... | (right 𝑇-te) = right (typecheck-lam.Success-te.Result Γ te 𝑇-te)

-- //


