
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement where

open import Verification.Conventions hiding (ℕ ; _⊔_)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition


-- | Given a HM term |t|, and a context |Γ|, the question is whether
--   there exists a type |τ| such that |Γ ⊢ t : τ|. But this is not directly
--   the statement we use because:
-- | - Types in the context may contain free variables, it is allowed to substitute
--     them. Such a need arises during the typechecking process, and
--     needs to be allowed in the statement. (We can reproduce the usual
--     statement of a fixed Γ, since we later know that the needed substitution
--     is minimal, ie. taking the result of the algorithm, we can check whether
--     context variables have been substituted, if not, we have the required statement
--     if they were, then there can be no type assignment which does not substitute them.)
-- | - Usually there are multiple types possible for a given term. We are thus not interested
--     in some type |τ|, but in all types which this term might have. The requirement is thus,
--     that the algorithm produces a principal type assignment, such that all other type assignments,
--     can be derived from it.

-- |: {}

-- [Definition]
-- | A type assignment is given by the following things:
record TypeAssignment {μs k} {Q : ℒHMQuant k} (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) : 𝒰₀ where
  constructor _/_⊩_,_,_,_
  field metas : ℒHMTypes
  field typeMetas : ℒHMTypes
  field ctx : ℒHMCtx Q (metas)
  field typ : ℒHMType (⟨ metas ⊔ typeMetas ⟩)
  field isInstance : Γ <Γ ctx
  field hasType : isTypedℒHM (metas ⊔ typeMetas ⊩ (ctx ⇃[ ι₀ ]⇂ᶜ) ⊢ typ) te

open TypeAssignment public
-- //

-- | In order to define what a principal type assignment is,
--   we require the notion of "morphism" between type assignments.

-- [Definition]
-- | Let ... be a lot of stuff.
module _ {μs k} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs} {te : UntypedℒHM k}  where
  -- | Then for two type assignments ... we define that ... if ....
  record _<TI_ (𝑇 : TypeAssignment Γ te) (𝑆 : TypeAssignment Γ te) : 𝒰₀ where
    field tiSubₐ : metas 𝑇 ⟶ metas 𝑆
    field tiSubₓ : typeMetas 𝑇 ⟶ metas 𝑆 ⊔ typeMetas 𝑆
    field typProof : typ 𝑇 ⇃[ ⦗ tiSubₐ ◆ ι₀ , tiSubₓ ⦘ ]⇂ ≡ typ 𝑆
    field subProof : isInstance 𝑇 .fst ◆ tiSubₐ ∼ isInstance 𝑆 .fst

-- //

-- [Hide]
    ctxProofTI : ctx 𝑇 ⇃[ tiSubₐ ]⇂ᶜ ≡ ctx 𝑆
    ctxProofTI = ctx 𝑇 ⇃[ tiSubₐ ]⇂ᶜ  ⟨ cong _⇃[ tiSubₐ ]⇂ᶜ (sym-Path (isInstance 𝑇 .snd)) ⟩-≡
                 Γ ⇃[ fst (isInstance 𝑇) ]⇂ᶜ ⇃[ tiSubₐ ]⇂ᶜ  ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                 Γ ⇃[ fst (isInstance 𝑇) ◆ tiSubₐ ]⇂ᶜ  ⟨ Γ ⇃[≀ subProof ≀]⇂ᶜ ⟩-≡
                 Γ ⇃[ fst (isInstance 𝑆) ]⇂ᶜ           ⟨ isInstance 𝑆 .snd ⟩-≡
                 ctx 𝑆 ∎-≡

  open _<TI_ public

-- //

-- [Definition]
-- | A /principal type assignment/ then is given by the following type:
PrincipalTypeAssignment : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) -> 𝒰₀
PrincipalTypeAssignment Γ te = ∑ λ (𝑇 : TypeAssignment Γ te) -> ∀(𝑆 : TypeAssignment Γ te) -> 𝑇 <TI 𝑆
-- //

-- [Definition]
-- | We say that a /type assignment decision/ for context, term
--   is an inhabitant of the following type.
TypeAssignmentDecision : ∀{μs k} -> {Q : ℒHMQuant k} -> (Γ : ℒHMCtx Q μs) (te : UntypedℒHM k) -> 𝒰₀
TypeAssignmentDecision Γ te = (TypeAssignment Γ te -> ⊥-𝒰 {ℓ₀}) + (PrincipalTypeAssignment Γ te)
-- |> That is, either a proof of the fact that there is not type assignment,
--    or a principal type assignment for the term.

-- //

-- [Lemma]
-- | Showing that such a decision exists for every term
--   is equivalent to showing that there is a sound and
--   complete type inference algorithm for the typing
--   rules.

-- //

-- [Proof]
-- | Soundness is given intrinsically by the fact
--   that an inhabitant of |PrincipalTypeAssignment Γ te|
--   carries a proof that there exists indeed a typing
--   derivation from the rules for the type it contains.
--   Completeness can be seen be easily seen: Assume there
--   is a type assignment, inspect the output of the algorithm,
--   we know that it cannot be a left term, since a type assignment
--   exists. Thus it must be a right term, which is a principal type
--   assignment, hence the given type assignment must be an instance of it.

-- //


-- [Theorem]
-- | There exists a function which, given |Γ| and |te|
--   produces a value of type |TypeAssignment Γ te|.

-- //


