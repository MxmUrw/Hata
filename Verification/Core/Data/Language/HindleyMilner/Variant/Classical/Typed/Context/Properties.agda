
{-# OPTIONS --experimental-lossy-unification #-}

module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties where


open import Verification.Conventions hiding (ℕ ; _⊔_ ; Σ)


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports


open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition



-- module _ {Σ : ℒHMSignature 𝑖} where
module _ {𝒯 : 𝒰 𝑖} {{_ : isℒHMTypeCtx {𝑗} 𝒯}} where

  private
    Σ : ℒHMSignature _
    Σ = ′ 𝒯 ′

  map-ℒHMCtx : ∀{n : ♮ℕ} -> {q : ℒHMQuant Σ n} {a b : ℒHMTypes Σ} -> a ⟶ b -> ℒHMCtx q a -> ℒHMCtx q b
  map-ℒHMCtx f [] = []
  map-ℒHMCtx f (c ∷ xs) = (c ⇃[ f ⇃⊔⇂ id ]⇂) ∷ (map-ℒHMCtx f xs)


  infixl 80 _⇃[_]⇂ᶜ

  _⇃[_]⇂ᶜ : ∀{k} -> ∀{a b : ℒHMTypes Σ} -> {Q : ℒHMQuant Σ k} -> ℒHMCtx Q a -> (a ⟶ b) -> ℒHMCtx Q b
  _⇃[_]⇂ᶜ x f = map-ℒHMCtx f x




  abstract
    _⇃[≀_≀]⇂ᶜ : ∀{k} {Q : ℒHMQuant Σ k} -> ∀{a b : ℒHMTypes Σ} -> (Γ : ℒHMCtx Q a) -> {f g : a ⟶ b}
                  -> f ∼ g -> Γ ⇃[ f ]⇂ᶜ ≡ Γ ⇃[ g ]⇂ᶜ
    _⇃[≀_≀]⇂ᶜ [] {f = f} {g} p = refl-≡
    _⇃[≀_≀]⇂ᶜ (c ∷ Γ) {f = f} {g} p = λ i -> lem-2 i ∷ (Γ ⇃[≀ p ≀]⇂ᶜ) i
      where
        lem-2 : c ⇃[ f ⇃⊔⇂ id ]⇂ ≡ c ⇃[ g ⇃⊔⇂ id ]⇂
        lem-2 = c ⇃[≀ p ≀⇃⊔⇂≀ refl ≀]⇂



    module _ {a b c : ℒHMTypes Σ} where
      functoriality-◆-⇃[]⇂ᶜ : ∀{k} {Q : ℒHMQuant Σ k} {Γ : ℒHMCtx Q a} -> {f : a ⟶ b} -> {g : b ⟶ c}
                              -> Γ ⇃[ f ]⇂ᶜ ⇃[ g ]⇂ᶜ ≡ Γ ⇃[ f ◆ g ]⇂ᶜ
      functoriality-◆-⇃[]⇂ᶜ {Γ = []} = refl-≡
      functoriality-◆-⇃[]⇂ᶜ {Q = _ ∷ _} {Γ = c ∷ Γ} {f = f} {g = g} = λ i → (lem-2 i) ∷ (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} {f = f} {g = g}) i
        where
          lem-2 : c ⇃[ f ⇃⊔⇂ id ]⇂ ⇃[ g ⇃⊔⇂ id ]⇂ ≡ c ⇃[ (f ◆ g) ⇃⊔⇂ id ]⇂
          lem-2 = c ⇃[ f ⇃⊔⇂ id ]⇂ ⇃[ g ⇃⊔⇂ id ]⇂   ⟨ functoriality-◆-⇃[]⇂ {τ = c} {f = f ⇃⊔⇂ id} {g = g ⇃⊔⇂ id} ⟩-≡
                  c ⇃[ (f ⇃⊔⇂ id) ◆ (g ⇃⊔⇂ id) ]⇂   ⟨ c ⇃[≀ functoriality-◆-⊔ ⁻¹ ≀]⇂ ⟩-≡
                  c ⇃[ ((f ◆ g) ⇃⊔⇂ (id ◆ id)) ]⇂       ⟨ c ⇃[≀ refl ≀⇃⊔⇂≀ unit-2-◆ ≀]⇂ ⟩-≡
                  c ⇃[ (f ◆ g) ⇃⊔⇂ id ]⇂            ∎-≡

    module _ {a : ℒHMTypes Σ} where
      functoriality-id-⇃[]⇂ᶜ : ∀{k} {Q : ℒHMQuant Σ k} {Γ : ℒHMCtx Q a} -> Γ ⇃[ id ]⇂ᶜ ≡ Γ
      functoriality-id-⇃[]⇂ᶜ {Γ = []} = refl-≡
      functoriality-id-⇃[]⇂ᶜ {Γ = c ∷ Γ} = λ i -> lem-2 i ∷ functoriality-id-⇃[]⇂ᶜ {Γ = Γ} i
        where
          lem-2 : c ⇃[ id ⇃⊔⇂ id ]⇂ ≡ c
          lem-2 = c ⇃[ id ⇃⊔⇂ id ]⇂   ⟨ c ⇃[≀ functoriality-id-⊔ ≀]⇂ ⟩-≡
                  c ⇃[ id ]⇂          ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                  c                   ∎-≡



  module §-ℒHMCtx where
    -------------------------------------------------
    -- lookup-commutation lemma, proof

    -- [Hide]
    abstract
      prop-2-proof : ∀{μs νs : ℒHMTypes Σ} {k} -> {Q : ℒHMQuant Σ k} -> {Γ : ℒHMCtx Q μs}
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
    module _ {μs νs : ℒHMTypes Σ} where

    -- |> Assume we have a size [..],
    --   a quantification [..] of that size,
    --   and a context [..] over that quantification.
      module _ {k} {Q : ℒHMQuant Σ k} {Γ : ℒHMCtx Q μs} where

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




