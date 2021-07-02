
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheoryMulti where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
-- open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition
-- open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition using (_∶_⊢_)
-- open import Verification.Experimental.Theory.Std.TypeTheory.Definition
-- open import Verification.Experimental.Computation.Question.Definition
-- open import Verification.Experimental.Computation.Question.Specific.Small

-- open import Verification.Experimental.Category.Std.Fibration.BaseChange.Definition
-- open import Verification.Experimental.Category.Std.Fibration.Definition
-- open import Verification.Experimental.Category.Std.Fibration.Instance.BaseChange

-- open import Verification.Experimental.Category.Std.Limit.Specific.Pullback
-- open import Verification.Experimental.Category.Std.Fibration.Specific.Fam.Definition
-- open import Verification.Experimental.Data.Universe.Everything

-- open import Verification.Experimental.Theory.Std.ProgrammingLanguage.Definition
-- open import Verification.Experimental.Category.Std.Graph.Definition

ctr-app : Info -> Info -> Maybe Info
ctr-app (Γ ⊢ (A ⇒ B)) (Γ' ⊢ A') with (Γ ≟ Γ') | (A ≟ A')
... | false | Y = nothing
... | true | false = nothing
... | true | true = just $ Γ ⊢ B
ctr-app _ _ = nothing


ctr-lam : Info -> Maybe Info
ctr-lam ((Γ , A) ⊢ B) = just $ Γ ⊢ (A ⇒ B)
ctr-lam _             = nothing

