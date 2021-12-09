
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.Infer where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.Monad

open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Instance.Monad

sᵘ : ℒHMJudgement -> ♮ℕ
sᵘ (_ ⊩ Γ ⊢ τ) = size-Listᴰ Γ

macro s = #structureOn sᵘ


ふ : 𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀ -> 𝐈𝐱 ♮ℕ 𝐔𝐧𝐢𝐯₀
ふ x = indexed (λ a -> ⟨ f a ⟩)
  where
    f : ♮ℕ -> 𝐂𝐚𝐭₀
    f n = 𝒟
      where
        𝒞'ᵘ  : 𝒰 _
        𝒞'ᵘ = ∑ λ (c : ℒHMJudgement) -> s c ≣ n

        Fᵘ : 𝒞'ᵘ -> ℒHMJudgement
        Fᵘ = fst

        𝒞' : 𝐂𝐚𝐭₀
        𝒞' = 𝒞'ᵘ since {!!}

        Gᵘ : 𝒞'ᵘ -> 𝐂𝐚𝐭₀
        Gᵘ (Γ , _) = ix x Γ since {!!}

        G : Functor 𝒞' (𝐂𝐚𝐭 _)
        G = Gᵘ since {!!}

        𝒟 = ⨊ G

-- indexed (λ n →  ∑ λ metas -> ∑ λ (Γ : 人Vecᵖ (ℒHMPolyType metas) n) -> ∑ λ (τ : ℒHMPolyType metas) -> x ⌄ (⟨ Γ ⟩ ⊢ τ))


instance
  isFunctor:ふ : isFunctor (𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀) (𝐈𝐱 ♮ℕ 𝐔𝐧𝐢𝐯₀) ふ
  isFunctor:ふ = {!!}

ま : 𝐈𝐱 ♮ℕ 𝐔𝐧𝐢𝐯₀ -> 𝐈𝐱 ℒHMJudgement 𝐔𝐧𝐢𝐯₀
ま = 写* s
-- (λ (Γ ⊢ τ) → map-⋆List (const tt) Γ)


π : ∀ A -> TypedℒHM (ま A) ⟶ ま (UntypedℒHM A)
π A (_ ⊩ Γ ⊢ τ) (var) = {!!} -- var (map-∍ (const tt) x)
π A (_ ⊩ Γ ⊢ τ) (hole x) = hole x
π A (_ ⊩ Γ ⊢ τ) (gen x te) = {!!}
π A (_ ⊩ Γ ⊢ (∀[ _ ] snd₁)) (app x y) = app (π _ _ x) (π _ _ y)
π A (_ ⊩ Γ ⊢ (∀[ _ ] .(_ ⇒ _))) (lam x) = lam (π _ _ x)
π A (_ ⊩ Γ ⊢ (∀[ _ ] .(_ ⇒ _))) (lam2 x) = lam (π _ _ x)
π A (_ ⊩ Γ ⊢ τ) (mapmeta x x₁) = {!!}
π A (_ ⊩ Γ ⊢ τ) (instantiate x te) = π _ _ te


γ : ∀ A -> UntypedℒHM A ⟶ ふ (TypedℒHM (ま (UntypedℒHM A)))
γ A = γᵘ
  where
    γᵘ : ∀ x -> UntypedℒHM A ⌄ x ⟶ ふ (TypedℒHM (ま (UntypedℒHM A))) ⌄ x
    γᵘ x (var) = {!!}
    γᵘ x (hole x₁) = {!!}
    γᵘ x (slet te te₁) = {!!}
    γᵘ x (app te te₁) = {!!}
    γᵘ x (lam te) with γᵘ {!!} te
    ... | ((μs ⊩ (∀[] α ∷ Γ) ⊢ ∀[ vβ ] β) , refl-≣) , tx

        -- = let tx1 : TypedℒHMᵈ _ (μs ⊩ (∀[] α ∷ Γ) ⊢ ∀[ vβ ] β)
        --       tx1 = tx
        --       tx2 : TypedℒHMᵈ _ ((μs ⊔ ι vβ) ⊩ mapOf (ℒHMCtx' _) ι₀ (∀[] α ∷' Γ) ⊢ mapOf ℒHMPolyType ι₀ (∀[ vβ ] β))
        --       tx2 = mapmeta ι₀ tx1

        --       tx3 : TypedℒHMᵈ _ ((μs ⊔ ι vβ) ⊩ mapOf (ℒHMCtx' _) ι₀ (∀[] α ∷' Γ) ⊢ mapOf ℒHMPolyType ι₀ (∀[] {!!}))
        --       tx3 = {!!}

        --       tx4 : TypedℒHMᵈ _ ((μs ⊔ ι vβ) ⊩ mapOf (ℒHMCtx' _) ι₀ Γ ⊢ mapOf ℒHMPolyType ι₀ (∀[] {!!} ⇒ {!!}))
        --       tx4 = lam tx3
          -- in {!!}

        = (μs ⊩ Γ ⊢ ∀[ vβ ] (α ⇃[ id {a = μs} ⇃⊔⇂ elim-⊥ ]⇂) ⇒ β , refl-≣) , lam2 tx

          -- (Γ ⊢ ∀[ vβ ] (α ⇃[ id ⇃⊔⇂ elim-⊥ ]⇂) ⇒ β , refl-≣) , (gen {!!} (lam {!!}))

    ... | ((μs ⊩ ((∀[ incl (x₁ ∷ ⟨_⟩₁) ] α) ∷ Γ) ⊢ (∀[ vβ ] β)) , refl-≣) , tx = {!!} , {!!}

{-

-- this is the type inference for ℒHM
module ℒHM-Inference where
  private
    -- ℒHMFin


    f : ∀ {A} metas n
        -> (Γ : 人Vecᵖ (ℒHMPolyType metas) n)
        -> UntypedℒHM A ⌄ n
        -> ∑ λ τ -> TypedℒHM (ま (UntypedℒHM A)) ⌄ (⟨ Γ ⟩ ⊢ τ)
    f {A} metas n Γ (var x) = _ , var (get-∍-人Vecᵖ Γ x)
    f {A} metas n Γ (hole x) = {!!} , (hole (hole {!!}))
    f {A} metas n Γ (slet te te₁) = {!!}
    f {A} metas n Γ (app te te₁) = {!!}
    f {A} metas n Γ (lam te) =
      let
          -- we create a new type variable
          -- by increasing the metas
          metas₁ = metas ⊔ st

          -- we embed the old context into
          -- the one containing the new variable
          Γ' = mapOf ℒHMCtx ι₀ ⟨ Γ ⟩

          -- the new context contains the new type variable
          Γ₁ = Γ' ⋆ incl (∀[ ⊥ ] (var (left-∍ (right-∍ incl))))

          -- we infer the type of the body of the lambda expression
          β , te' = f metas₁ _ (vecᵖ Γ₁ {!!}) te

      in {!!}


infer-TypedℒHM : ∀ A -> UntypedℒHM A ⟶ ふ (TypedℒHM (ま (UntypedℒHM A)))
infer-TypedℒHM A x te = {!!} , {!!} , {!!} , {!!}




-}

