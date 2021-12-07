
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition where


open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition

open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties

open import Verification.Core.Order.Preorder

----------------------------------------------------------------------------------
-- Definition of the Hindley Milner type system
--

-- | The type system as displayed in \ref{} contains the rules /inst/ and /gen/,
--   which can be applied in between any derivation steps, and are not mentioned
--   in the term. This makes it more difficult to deal with typing derivations
--   for a given term |t|, as different derivation trees for the same typing exist.
--
-- | In the proof of completeness of algorithm W in \cite{Damas:1984}, it is mentioned
--   that it is enough to show that the algorithm derives a typing which is more general
--   than any other given typing derivation |Δ ⊢ τ|, when that given typing derivation
--   does not contain an /inst/ or /gen/ rule.
--
-- | A slightly different approach is taken in \cite{CDDK:1986}, where it is first shown
--   that an alternative set of typing rules \ref{}, without the "term-less" rules /inst/
--   and /gen/ may be used instead, in the sense that a principal type for this typing system
--   is also a principal typing system for the original rules.
--   \begin{align}
--       Γ ⊢' τ &⟹ Γ ⊢ τ \\
--       Γ ⊢ τ \text{ (principal)} &⟹ Γ ⊢' τ \text{ (principal)}
--   \end{align}
--
-- | We thus use this alternative typing system in our implementation, and
--   show that our algorithm derives a principal typing with regards to it.


----------------------------------------------------------------------------------
-- Prereqs
--

-- | First we define a record type to hold judgement statements

-- [Definition]
-- | A /judgement statement/ is an element of the type [..], which
--   is defined by
record ℒHMJudgement : 𝒰₀ where
  constructor _⊩_⊢_
  -- | - A list of metavariables [..].
  field metavars : ℒHMTypes
  -- | - A size for the context [..].
  field {contextsize} : ♮ℕ
  -- | - A context [..] containing |contextsize| many types,
  --     each of which may use metavariables from |metavars|.
  field context : ℒHMCtx contextsize metavars
  -- field quantifiers : Listᴰ (const (ℒHMTypes)) contextsize
  -- field context : Listᴰ² (λ a -> ℒHMType ⟨ a ⟩) quantifiers

  -- | - A type [..] representing the "return type" of the
  --     judgement, using the same metavars as the context.
  field type : ℒHMType ⟨ metavars ⟩

open ℒHMJudgement public
-- //

-- [Notation]
-- | We define the following function to return the
--   size of a context.
s : ℒHMJudgement -> ♮ℕ
s (_ ⊩ Γ ⊢ τ) = size-Listᴰ (fst Γ)

-- //


-- [Hide]
pattern _∷'_ x xs = _∷_ {a = tt} x xs

-- //

-- [Definition]
-- | We define an /abstraction of metavariables/.
record isAbstr {k} {Q : ℒHMQuant k} (κs : ℒHMTypes) {μs₀ μs₁} (Γ₀ : ℒHMCtxFor Q μs₀) (Γ₁ : ℒHMCtxFor Q μs₁)
               (τ₀ : ℒHMType ⟨ μs₀ ⟩) (τ₁ : ℒHMType ⟨ μs₁ ⊔ κs ⟩) : 𝒰₀ where
  constructor isAbstr:byDef
  field metasProof : μs₀ ≅ (μs₁ ⊔ κs)
  field ctxProof : Γ₀ ⇃[ ⟨ metasProof ⟩ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
  field typeProof : τ₀ ⇃[ ⟨ metasProof ⟩ ]⇂ ≡ τ₁

  inverseCtxProof : Γ₀ ≡ Γ₁ ⇃[ ι₀ ◆ ⟨ metasProof ⟩⁻¹ ]⇂ᶜ
  inverseCtxProof = {!!}

open isAbstr public
-- //

-- [Hide]
module §-isAbstr where
  prop-1 : ∀{k} {Q : ℒHMQuant k} {κs : ℒHMTypes} {μs₀ μs₁ μs₂} {Γ₀ : ℒHMCtxFor Q μs₀} {Γ₁ : ℒHMCtxFor Q μs₁}
               {τ₀ : ℒHMType ⟨ μs₀ ⟩} {τ₁ : ℒHMType ⟨ μs₁ ⊔ κs ⟩}
           -> (σ₁₂ : μs₁ ⟶ μs₂)
           -> isAbstr κs Γ₀ Γ₁ τ₀ τ₁
           -> isAbstr κs Γ₀ (Γ₁ ⇃[ σ₁₂ ]⇂-CtxFor) τ₀ (τ₁ ⇃[ σ₁₂ ⇃⊔⇂ id ]⇂)
  prop-1 = {!!}

-- //



-- [Definition]
-- | We define the hindley milner typing relation for lambda terms.
data isTypedℒHM : (Γ : ℒHMJudgement) -> (te : UntypedℒHM (s Γ)) -> 𝒰₀ where
-- | - Variable terms.
  var  : ∀{μs k i} -> {Q : ℒHMQuant k}
         -> {Γ : ℒHMCtxFor Q μs}
         -> (k∍i : k ∍♮ i)
         -> (σ : (lookup-Listᴰ Q k∍i) ⟶ μs)
         -> ∀{α}
         -> lookup-Listᴰ² Γ k∍i ⇃[ ⦗ id , σ ⦘ ]⇂ ≡ α
         -> isTypedℒHM ((μs) ⊩ (Q , Γ) ⊢ α) (var k∍i)

-- | - Application terms.
  app : ∀{μs k te₀ te₁} {Γ : ℒHMCtx k μs} {α β : ℒHMType ⟨ μs ⟩}
        -> isTypedℒHM (μs ⊩ Γ ⊢ (α ⇒ β)) te₀
        -> isTypedℒHM (μs ⊩ Γ ⊢ α) te₁
        -> isTypedℒHM (μs ⊩ Γ ⊢ β) (app te₀ te₁)

-- | - Lambda terms.
  lam : ∀{μs k te} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μs}
         {α : ℒHMType ⟨ μs ⊔ ⊥ ⟩}
         {β : ℒHMType ⟨ μs ⟩}
         -> isTypedℒHM (μs ⊩ (⊥ ∷' Q , α ∷ Γ) ⊢ β) te
         -> isTypedℒHM (μs ⊩ (Q , Γ) ⊢ α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β) (lam te)

-- | - Let terms.
  slet : ∀{μs κs νs k te₀ te₁}
        -> {Q : ℒHMQuant k}
        -> {Γ : ℒHMCtxFor Q μs} {Γ' : ℒHMCtxFor Q νs}
        -> {α : ℒHMType ⟨ μs ⟩}
        -> {α' : ℒHMType ⟨ νs ⊔ κs ⟩}
        -> {β : ℒHMType ⟨ νs ⟩}
        -> isAbstr (κs) (Γ) (Γ') α α'
        -> isTypedℒHM (μs ⊩ (Q , Γ) ⊢ α) te₀
        -> isTypedℒHM (νs ⊩ (κs ∷' Q , α' ∷ Γ') ⊢ β) te₁
        -> isTypedℒHM (νs ⊩ (Q , Γ') ⊢ β) (slet te₀ te₁)
-- //


-- [Lemma]
-- | We can substitute meta variables inside of
--   contexts.
transp-isTypedℒHM : ∀{k μs te} {Q : ℒHMQuant k}
         -> {Γ₀ : ℒHMCtxFor Q μs} {τ₀ : ℒHMType ⟨ μs ⟩}
         -> {Γ₁ : ℒHMCtxFor Q μs} {τ₁ : ℒHMType ⟨ μs ⟩}
         -> Γ₀ ≡ Γ₁ -> τ₀ ≡ τ₁
         -> isTypedℒHM (μs ⊩ (_ , Γ₀) ⊢ τ₀) te
         -> isTypedℒHM (μs ⊩ (_ , Γ₁) ⊢ τ₁) te
transp-isTypedℒHM = {!!}
-- //




-- [Hide]
-- | Some properties of the typing relation.
module §-isTypedℒHM where
  abstract
    prop-1 : ∀{μs k} -> {Γ : ℒHMCtx k μs} {τ : ℒHMType ⟨ μs ⟩}
            -> ∀ te
            -> isTypedℒHM (μs ⊩ Γ ⊢ τ) (lam te)
            -> ∑ λ νs -> ∑ λ (Δ : ℒHMCtx (tt ∷ k) νs) -> ∑ λ (τ' : ℒHMType ⟨ νs ⟩)
            -> isTypedℒHM (νs ⊩ Δ ⊢ τ') te
    prop-1 te (lam p) = {!!} , ({!!} , ({!!} , p))


    prop-2 : ∀{k μs νs te} {Γ : ℒHMCtx k μs} {τ : ℒHMType ⟨ μs ⟩}
          -> (σ : μs ⟶ νs)
          -> isTypedℒHM (μs ⊩ Γ ⊢ τ) te
          -> isTypedℒHM (νs ⊩ (Γ ⇃[ σ ]⇂-Ctx) ⊢ (τ ⇃[ σ ]⇂)) te
    prop-2 σ (var x xp ρ) = {!!}
    prop-2 σ (app te se) = {!!}
      -- let te' = prop-2 σ te
      --     se' = prop-2 σ se
      -- in app te' se'
    prop-2 σ (lam te) = {!!}
    prop-2 σ (slet ab set te) = {!!}

    prop-4 : ∀{k μsₐ μsₓ νsₓ νsₐ te} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μsₐ} {τ : ℒHMType ⟨ μsₐ ⊔ μsₓ ⟩}
          -> (σₐ : μsₐ ⟶ νsₐ)
          -> (σₓ : μsₓ ⟶ νsₓ)
          -> isTypedℒHM (μsₐ ⊔ μsₓ ⊩ (_ , Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ τ) te
          -> isTypedℒHM (νsₐ ⊔ νsₓ ⊩ (_ , Γ ⇃[ σₐ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ (τ ⇃[ σₐ ⇃⊔⇂ σₓ ]⇂)) te
    prop-4 = {!!}

    prop-3 : ∀{k μsₐ μsₓ νsₓ te} {Q : ℒHMQuant k} {Γ : ℒHMCtxFor Q μsₐ} {τ : ℒHMType ⟨ μsₐ ⊔ μsₓ ⟩}
          -> (σ : μsₓ ⟶ νsₓ)
          -> isTypedℒHM (μsₐ ⊔ μsₓ ⊩ (_ , Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ τ) te
          -> isTypedℒHM (μsₐ ⊔ νsₓ ⊩ (_ , Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ (τ ⇃[ id ⇃⊔⇂ σ ]⇂)) te
    prop-3 = {!!}

-- //

