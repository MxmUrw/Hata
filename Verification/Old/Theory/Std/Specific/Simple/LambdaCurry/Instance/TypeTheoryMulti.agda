
module Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheoryMulti where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Instance.Category
-- open import Verification.Core.Theory.Std.Presentation.Signature.SingleSorted.Definition
open import Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Definition
-- open import Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Definition using (_∶_⊢_)
-- open import Verification.Core.Theory.Std.TypeTheory.Definition
-- open import Verification.Core.Computation.Question.Definition
-- open import Verification.Core.Computation.Question.Specific.Small

-- open import Verification.Core.Category.Std.Fibration.BaseChange.Definition
-- open import Verification.Core.Category.Std.Fibration.Definition
-- open import Verification.Core.Category.Std.Fibration.Instance.BaseChange

-- open import Verification.Core.Category.Std.Limit.Specific.Pullback
-- open import Verification.Core.Category.Std.Fibration.Specific.Fam.Definition
-- open import Verification.Core.Data.Universe.Everything

-- open import Verification.Core.Theory.Std.ProgrammingLanguage.Definition
-- open import Verification.Core.Category.Std.Graph.Definition

ctr-app : Info -> Info -> Maybe Info
ctr-app (Γ ⊢ (A ⇒ B)) (Γ' ⊢ A') with (Γ ≟ Γ') | (A ≟ A')
... | false | Y = nothing
... | true | false = nothing
... | true | true = just $ Γ ⊢ B
ctr-app _ _ = nothing


ctr-lam : Info -> Maybe Info
ctr-lam ((Γ , A) ⊢ B) = just $ Γ ⊢ (A ⇒ B)
ctr-lam _             = nothing

