
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Case.Var where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports


open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Statement
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Definition2

open import Verification.Core.Order.Preorder

-- [Lemma]
-- | "Inversion of Var"

inv-var : ∀{k μs} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs}
          -> {α : ℒHMType ⟨ μs ⟩}
          -> ∀{i} -> {k∍i : k ∍♮ i}
          -> isTypedℒHM (μs ⊩ Γ ⊢ α) (var k∍i)
          -> ∑ λ (σ : (lookup-Listᴰ Q k∍i) ⟶ μs)
             -> lookup-Listᴰ² Γ k∍i ⇃[ ⦗ id , σ ⦘ ]⇂ ≡ α
inv-var (var _ σ x) = σ , x

-- //


module §-ℒHMCtx where
  -------------------------------------------------
  -- lookup-commutation lemma, proof

  -- [Hide]
  abstract
    prop-2-proof : ∀{μs νs : ℒHMTypes} {k} -> {Q : ℒHMQuant k} -> {Γ : ℒHMCtx Q μs}
                    -> ∀{i} -> (k∍i : k ∍♮ i)
                    -> ∀ (σ₀ : μs ⟶ νs)
                    -> ∀ (σ₁ : lookup-Listᴰ Q k∍i ⟶ νs)
                    -> lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
                      ≡
                      lookup-Listᴰ² (Γ ⇃[ σ₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , σ₁ ⦘ ]⇂

    prop-2-proof {Γ = b ∷ Γ} incl σ₀ σ₁ =

      let lem-0 : (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ∼ ⦗ σ₀ , σ₁ ⦘
          lem-0 = (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘   ⟨ append-⇃⊔⇂ {f0 = σ₀} {id} {id} {σ₁} ⟩-∼
                  ⦗ σ₀ ◆ id , id ◆ σ₁ ⦘       ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (unit-r-◆ {f = σ₀} , unit-l-◆ {f = σ₁}) ⟩-∼
                  ⦗ σ₀ , σ₁ ⦘                 ∎

          lem-1 : b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂ ≡ b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
          lem-1 = b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = b} {f = (σ₀ ⇃⊔⇂ id)} {g = ⦗ id , σ₁ ⦘} ⟩-≡
                  b ⇃[ (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ]⇂      ⟨ b ⇃[≀ lem-0 ≀]⇂ ⟩-≡
                  b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂                    ∎-≡
      in sym-Path lem-1

    prop-2-proof {Γ = b ∷ Γ} (skip k∍i) σ₀ σ₁ = prop-2-proof {Γ = Γ} k∍i σ₀ σ₁

-- //


  -------------------------------------------------
  -- lookup-commutation lemma, description

  -- [Lemma]
  -- | Let [..] be metavariables.
  module _ {μs νs : ℒHMTypes} where

  -- |> Assume we have a size [..],
  --   a quantification [..] of that size,
  --   and a context [..] over that quantification.
    module _ {k} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q μs} where

  -- |> Let [..] and [..] describe an element of that context.
      module _ {i} (k∍i : k ∍♮ i) where

  -- | Now if there are two substitutions [..] and [..],
  --   such that |⦗ σ₀ , σ₁ ⦘| can be applied to
  --   the type of the |k| entry of the context,
        module _ (σ₀ : μs ⟶ νs) (σ₁ : lookup-Listᴰ Q k∍i ⟶ νs) where

  -- |> then applying these two substitutions after looking
  --   up the type of |k| is the same as first applying |σ₀|
  --   to the whole context, then looking up that value,
  --   and then applying |σ₁| on the bound variables of the |k| entry.
          prop-2 : lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
                    ≡
                    lookup-Listᴰ² (Γ ⇃[ σ₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , σ₁ ⦘ ]⇂
          prop-2 = prop-2-proof {Γ = Γ} k∍i σ₀ σ₁
  -- //

  -- [Proof]
  -- | The proof goes by induction on the context, and merely involves some
  --   coproduct related equational reasoning.

  -- //




-- [Lemma]
-- | Typechecking the /var/ case.
--   Let [..], [..], [..], [..] be the input of the
--   algorithm.
module typecheck-Var {μs : ℒHMTypes} {k : ♮ℕ} {Q : ℒHMQuant k} (Γ : ℒHMCtx Q μs) where

  -- |> Furthermore, assume
  --    that we have [..] and [..].
  module _ {i : ⊤-𝒰} (k∍i : k ∍♮ i) where
    -- |> Then the term |var k∍i| has a principal typing instance.

    --  //

    -- [Proof]
    -- | Define all the following things.
    vα = lookup-Listᴰ Q k∍i
    α = lookup-Listᴰ² Γ k∍i
    σᵤ₀ : μs ⟶ μs ⊔ vα
    σᵤ₀ = ι₀

    α₀ = α ⇃[ id ]⇂

    Γ₀ : ℒHMCtx Q (μs ⊔ vα)
    Γ₀ = Γ ⇃[ ι₀ ]⇂ᶜ

    Γ<Γ₀ : Γ <Γ Γ₀
    Γ<Γ₀ = record { fst = σᵤ₀ ; snd = refl-≡ }

    -- | We also have a proof of [..] [].
    lem-1 : lookup-Listᴰ² (Γ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ι₁ ⦘ ]⇂ ≡ lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂
    lem-1 = trans-Path (sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i ι₀ ι₁)) (lookup-Listᴰ² Γ k∍i ⇃[≀ §-ℒHMTypes.prop-1 ⁻¹ ≀]⇂)

    -- | This means that we have a typing instance.
    𝑇 : CtxTypingInstance Γ (var k∍i)
    𝑇 = (μs / vα ⊩ Γ , α₀ , reflexive , var k∍i ι₁ lem-1)

    -- | Now assume that [..] is another given typing instance.
    module _ (𝑆@(μs₁ / να₁ ⊩ Γ₁ , α₁ , Γ<Γ₁ , varP) : CtxTypingInstance Γ (var k∍i)) where

      -- | In particular, since |varP| is a proof that |Γ₁ ⊢ var k∍i : α₁|,
      --   we know that the derivation must have been given by a |var| constructor,
      --   and thus we know that there must be the following substitution,
      --   together with a proof that under this substitution,
      --   indeed the type |α₁| is the result.
      IP : ∑ λ (ρ : (lookup-Listᴰ Q k∍i) ⟶ (μs₁ ⊔ να₁))
           -> lookup-Listᴰ² (Γ₁ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂ ≡ α₁
      IP = inv-var varP

      -- | Let us call the substitution [..], and the proof [..].
      ρ = IP .fst
      ρp = IP .snd

      -- | We now have to give a substitution from the metavariables
      --   of our proposedly initial typing instance |𝑇| to the given
      --   typing instance |𝑆|, namely [..]. But since |𝑇| uses the same
      --   variables (for the context) as the input for the algorithm, |Γ|,
      --   such a substitution is given exactly by the proof of |Γ<Γ₁|
      --   of |𝑆|.
      σᵤ₁ : μs ⟶ μs₁
      σᵤ₁ = Γ<Γ₁ .fst

      -- | Next, we have ...
      lem-4 : Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
      lem-4 = Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ}) ⟩-≡
              Γ ⇃[ σᵤ₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ⟨ cong _⇃[ ι₀ {b = να₁} ]⇂ᶜ (Γ<Γ₁ .snd) ⟩-≡
              Γ₁ ⇃[ ι₀ ]⇂ᶜ           ∎-≡

      -- | And also ...

      lem-5 : lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ ≡ α₁
      lem-5 = lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

              ⟨ cong _⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ (functoriality-id-⇃[]⇂ {τ = lookup-Listᴰ² Γ k∍i}) ⟩-≡
              lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

              ⟨ (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i (σᵤ₁ ◆ ι₀) (ρ)) ⟩-≡

              lookup-Listᴰ² (Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

              ⟨ cong (λ ξ -> lookup-Listᴰ² ξ k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂) lem-4 ⟩-≡

              lookup-Listᴰ² (Γ₁ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

              ⟨ ρp ⟩-≡

              α₁

              ∎-≡

      -- | Which means that we have a proof of initiality.
      Result : 𝑇 <TI 𝑆
      Result = record { tiSubₐ = σᵤ₁ ; tiSubₓ = ρ ; typProof = lem-5 ; subProof = unit-l-◆ }

-- //



