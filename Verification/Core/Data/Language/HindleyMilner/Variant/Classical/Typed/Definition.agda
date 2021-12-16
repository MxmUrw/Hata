
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.MetaVarReduction


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

-- | First we define a record type to hold typing statements.

-- [Definition]
-- | A /typing statement/ is an element of the type [..], which
--   is defined by
record ℒHMJudgement : 𝒰₀ where
  constructor _⊩_⊢_
  -- | - A list of metavariables [..].
  field metavars : ℒHMTypes
  -- | - A size for the context [..].
  field {contextsize} : ♮ℕ
  -- | - A context [..] containing |contextsize| many types,
  --     each of which may use metavariables from |metavars|.
  field {quant} : ℒHMQuant contextsize
  field context : ℒHMCtx quant metavars
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
s j = contextsize j

-- //


-- [Hide]
pattern _∷'_ x xs = _∷_ {a = tt} x xs

-- //




-- [Definition]
-- | We define the hindley milner typing relation for lambda terms.
data isTypedℒHM : (Γ : ℒHMJudgement) -> (te : UntypedℒHM (s Γ)) -> 𝒰₀ where
-- | - Variable terms.
  var  : ∀{μs k i} -> {Q : ℒHMQuant k}
         -> {Γ : ℒHMCtx Q μs}
         -> (k∍i : k ∍♮ i)
         -> (σ : (lookup-Listᴰ Q k∍i) ⟶ μs)
         -> ∀{α}
         -> lookup-Listᴰ² Γ k∍i ⇃[ ⦗ id , σ ⦘ ]⇂ ≡ α
         -> isTypedℒHM ((μs) ⊩ Γ ⊢ α) (var k∍i)

-- | - Application terms.
  app : ∀{μs k te₀ te₁} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs} {α β : ℒHMType ⟨ μs ⟩}
        -> isTypedℒHM (μs ⊩ Γ ⊢ (α ⇒ β)) te₀
        -> isTypedℒHM (μs ⊩ Γ ⊢ α) te₁
        -> isTypedℒHM (μs ⊩ Γ ⊢ β) (app te₀ te₁)

-- | - Lambda terms.
  lam : ∀{μs k te} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs}
         {α : ℒHMType ⟨ μs ⊔ ⊥ ⟩}
         {β : ℒHMType ⟨ μs ⟩}
         -> isTypedℒHM (μs ⊩ α ∷ Γ ⊢ β) te
         -> isTypedℒHM (μs ⊩ Γ ⊢ α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β) (lam te)

-- | - Let terms.
  slet : ∀{μs κs νs k te₀ te₁}
        -> {Q : ℒHMQuant k}
        -> {Γ : ℒHMCtx Q μs} {Γ' : ℒHMCtx Q νs}
        -> {α : ℒHMType ⟨ μs ⟩}
        -> {α' : ℒHMType ⟨ νs ⊔ κs ⟩}
        -> {β : ℒHMType ⟨ νs ⟩}
        -> isAbstr (κs) (Γ) (Γ') α α'
        -> isTypedℒHM (μs ⊩ Γ ⊢ α) te₀
        -> isTypedℒHM (νs ⊩ (α' ∷ Γ') ⊢ β) te₁
        -> isTypedℒHM (νs ⊩ Γ' ⊢ β) (slet te₀ te₁)
-- //


-- [Lemma]
-- | We can transport along equalities of contexts and
--   types.
transp-isTypedℒHM : ∀{k μs te} {Q : ℒHMQuant k}
         -> {Γ₀ : ℒHMCtx Q μs} {τ₀ : ℒHMType ⟨ μs ⟩}
         -> {Γ₁ : ℒHMCtx Q μs} {τ₁ : ℒHMType ⟨ μs ⟩}
         -> Γ₀ ≡ Γ₁ -> τ₀ ≡ τ₁
         -> isTypedℒHM (μs ⊩ Γ₀ ⊢ τ₀) te
         -> isTypedℒHM (μs ⊩ Γ₁ ⊢ τ₁) te
transp-isTypedℒHM {μs = μs} {te = te} Γ τ Γ₀⊢τ₀ = transport (λ i -> isTypedℒHM (μs ⊩ Γ i ⊢ τ i) te) Γ₀⊢τ₀
-- //




-- [Hide]
-- | Some properties of the typing relation.
module §-isTypedℒHM where

  abstract
    prop-2 : ∀{k μs νs te} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs} {τ : ℒHMType ⟨ μs ⟩}
          -> (σ : μs ⟶ νs)
          -> isTypedℒHM (μs ⊩ Γ ⊢ τ) te
          -> isTypedℒHM (νs ⊩ (Γ ⇃[ σ ]⇂ᶜ) ⊢ (τ ⇃[ σ ]⇂)) te
    prop-2 {Γ = Γ} {τ = τ} σ (var x xp ρ) = var x (xp ◆ σ) lem-1
      where
        lem-0 : ⦗ σ , xp ◆ σ ⦘ ∼ ⦗ id , xp ⦘ ◆ σ
        lem-0 = ⦗ σ , xp ◆ σ ⦘      ⟨ ⦗≀ unit-l-◆ ⁻¹ , refl ≀⦘ ⟩-∼
                ⦗ id ◆ σ , xp ◆ σ ⦘ ⟨ append-⦗⦘ ⁻¹ ⟩-∼
                ⦗ id , xp ⦘ ◆ σ     ∎

        lem-1 : lookup-Listᴰ² (Γ ⇃[ σ ]⇂ᶜ) x ⇃[ ⦗ id , xp ◆ σ ⦘ ]⇂ ≡ τ ⇃[ σ ]⇂
        lem-1 = lookup-Listᴰ² (Γ ⇃[ σ ]⇂ᶜ) x ⇃[ ⦗ id , xp ◆ σ ⦘ ]⇂   ⟨ sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ} x σ (xp ◆ σ)) ⟩-≡
                lookup-Listᴰ² Γ x ⇃[ ⦗ σ , xp ◆ σ ⦘ ]⇂               ⟨ lookup-Listᴰ² Γ x ⇃[≀ lem-0 ≀]⇂ ⟩-≡
                lookup-Listᴰ² Γ x ⇃[ ⦗ id , xp ⦘ ◆ σ ]⇂              ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = lookup-Listᴰ² Γ x}) ⟩-≡
                lookup-Listᴰ² Γ x ⇃[ ⦗ id , xp ⦘ ]⇂ ⇃[ σ ]⇂          ⟨ cong _⇃[ σ ]⇂ ρ ⟩-≡
                τ ⇃[ σ ]⇂                                            ∎-≡

    prop-2 σ (app te se) = app (transp-isTypedℒHM refl-≡ §-⇃[]⇂.prop-1 (prop-2 σ te)) (prop-2 σ se)
    prop-2 σ (lam {α = α} {β = β} te) =
      let P = prop-2 σ te
          lem-1 : α ⇃[ σ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ≡ α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ σ ]⇂
          lem-1 = α ⇃[ σ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂   ⟨ functoriality-◆-⇃[]⇂ {τ = α} ⟩-≡
                  α ⇃[ (σ ⇃⊔⇂ id) ◆ ⦗ id , elim-⊥ ⦘   ]⇂   ⟨ α ⇃[≀ append-⇃⊔⇂ ≀]⇂ ⟩-≡
                  α ⇃[ ⦗ (σ ◆ id) , (id ◆ elim-⊥) ⦘    ]⇂   ⟨ α ⇃[≀ ⦗≀ unit-r-◆ ∙ unit-l-◆ ⁻¹ , expand-⊥ ∙ expand-⊥ ⁻¹ ≀⦘ ≀]⇂ ⟩-≡
                  α ⇃[ ⦗ (id ◆ σ) , (elim-⊥ ◆ σ) ⦘    ]⇂   ⟨ α ⇃[≀ append-⦗⦘ ⁻¹ ≀]⇂ ⟩-≡
                  α ⇃[ ⦗ id , elim-⊥ ⦘ ◆ σ ]⇂               ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α}) ⟩-≡
                  α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇃[ σ ]⇂          ∎-≡

          lem-3 :  α ⇃[ σ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β ⇃[ σ ]⇂ ≡ (α ⇃[ ⦗ id , elim-⊥ ⦘ ]⇂ ⇒ β) ⇃[ σ ]⇂
          lem-3 = trans-Path (cong (_⇒ β ⇃[ σ ]⇂) lem-1) (sym-Path §-⇃[]⇂.prop-1)

      in transp-isTypedℒHM refl-≡ lem-3 (lam P)
    prop-2 {μs = μs} {Γ = Γ} σ (slet {Γ = Γ₁} {α = α} {α' = α'} ab te se) =
      let ϕ = metasProof ab
          σ' : _ ⟶ _
          σ' = ⟨ ϕ ⟩ ◆ (σ ⇃⊔⇂ id)

          P-te = prop-2 σ' te
          P-se = prop-2 σ se

          lem-0 : Γ₁ ⇃[ σ' ]⇂ᶜ ⇃[ id ]⇂ᶜ ≡ Γ ⇃[ σ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
          lem-0 = Γ₁ ⇃[ σ' ]⇂ᶜ ⇃[ id ]⇂ᶜ           ⟨ functoriality-id-⇃[]⇂ᶜ ⟩-≡
                  Γ₁ ⇃[ σ' ]⇂ᶜ                     ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ₁}) ⟩-≡
                  Γ₁ ⇃[ ⟨ ϕ ⟩ ]⇂ᶜ ⇃[ σ ⇃⊔⇂ id ]⇂ᶜ  ⟨ cong _⇃[ σ ⇃⊔⇂ id ]⇂ᶜ (ctxProof ab) ⟩-≡
                  Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σ ⇃⊔⇂ id ]⇂ᶜ     ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                  Γ ⇃[ ι₀ ◆ (σ ⇃⊔⇂ id) ]⇂ᶜ        ⟨ Γ ⇃[≀ reduce-ι₀ ≀]⇂ᶜ ⟩-≡
                  Γ ⇃[ σ ◆ ι₀ ]⇂ᶜ                 ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ}) ⟩-≡
                  Γ ⇃[ σ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ            ∎-≡

          lem-1 : α ⇃[ σ' ]⇂ ⇃[ id ]⇂ ≡ α' ⇃[ σ ⇃⊔⇂ id ]⇂
          lem-1 = α ⇃[ σ' ]⇂ ⇃[ id ]⇂           ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                  α ⇃[ σ' ]⇂                     ⟨ sym-Path (functoriality-◆-⇃[]⇂ {τ = α}) ⟩-≡
                  α ⇃[ ⟨ ϕ ⟩ ]⇂ ⇃[ σ ⇃⊔⇂ id ]⇂  ⟨ cong _⇃[ σ ⇃⊔⇂ id ]⇂ (typeProof ab) ⟩-≡
                  α' ⇃[ σ ⇃⊔⇂ id ]⇂           ∎-≡

          ab-2 : isAbstr _ (Γ₁ ⇃[ σ' ]⇂ᶜ) (Γ ⇃[ σ ]⇂ᶜ) _ _
          ab-2 = isAbstr:byDef refl-≅ lem-0 lem-1

      in (slet ab-2 P-te P-se)

    prop-4 : ∀{k μsₐ μsₓ νsₓ νsₐ te} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μsₐ} {τ : ℒHMType ⟨ μsₐ ⊔ μsₓ ⟩}
          -> (σₐ : μsₐ ⟶ νsₐ)
          -> (σₓ : μsₓ ⟶ νsₓ)
          -> isTypedℒHM (μsₐ ⊔ μsₓ ⊩ (Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ τ) te
          -> isTypedℒHM (νsₐ ⊔ νsₓ ⊩ (Γ ⇃[ σₐ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ) ⊢ (τ ⇃[ σₐ ⇃⊔⇂ σₓ ]⇂)) te
    prop-4 {Γ = Γ} σₐ σₓ p =
      let lem-0 : Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σₐ ⇃⊔⇂ σₓ ]⇂ᶜ ≡ Γ ⇃[ σₐ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ
          lem-0 = Γ ⇃[ ι₀ ]⇂ᶜ ⇃[ σₐ ⇃⊔⇂ σₓ ]⇂ᶜ   ⟨ functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} ⟩-≡
                  Γ ⇃[ ι₀ ◆ (σₐ ⇃⊔⇂ σₓ) ]⇂ᶜ      ⟨ Γ ⇃[≀ reduce-ι₀ ≀]⇂ᶜ ⟩-≡
                  Γ ⇃[ σₐ ◆ ι₀ ]⇂ᶜ               ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ}) ⟩-≡
                  Γ ⇃[ σₐ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ          ∎-≡
      in p
        ⟪ prop-2 (σₐ ⇃⊔⇂ σₓ) ⟫
        ⟪ transp-isTypedℒHM lem-0 refl-≡ ⟫

    prop-3 : ∀{k μsₐ μsₓ νsₓ te} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μsₐ} {τ : ℒHMType ⟨ μsₐ ⊔ μsₓ ⟩}
          -> (σ : μsₓ ⟶ νsₓ)
          -> isTypedℒHM (μsₐ ⊔ μsₓ ⊩ (Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ τ) te
          -> isTypedℒHM (μsₐ ⊔ νsₓ ⊩ (Γ ⇃[ ι₀ ]⇂ᶜ) ⊢ (τ ⇃[ id ⇃⊔⇂ σ ]⇂)) te
    prop-3 {Γ = Γ} σ p =
      let
          lem-00 : Γ ⇃[ id ]⇂ᶜ ≡  Γ
          lem-00 = functoriality-id-⇃[]⇂ᶜ

          lem-0 : Γ ⇃[ id ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ≡  Γ ⇃[ ι₀ ]⇂ᶜ
          lem-0 = (cong _⇃[ ι₀ ]⇂ᶜ lem-00)

      in p
        ⟪ prop-4 {Γ = Γ} id σ ⟫
        ⟪ transp-isTypedℒHM lem-0 refl-≡ ⟫

-- //

