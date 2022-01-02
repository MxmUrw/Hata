
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Example.Simple where

open import Verification.Conventions hiding (ℕ ; _⊔_)

open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Main
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers

t-0 : UntypedℒHM 0
t-0 = slet (lam (var incl)) (app (var incl) (var incl))

Empty : ℒHMCtx [] (incl ◌)
Empty = []

result-t-0 = γ Empty t-0



