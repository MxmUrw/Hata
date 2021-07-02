
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.MTC where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
-- open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition
import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition as Λ
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition hiding (_⇒_)
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition
open import Verification.Experimental.Theory.Std.TypeTheory.Definition


module Λ-Curry where

  data Kind : 𝒰₀ where
    Te : Kind
    VarSuc : Kind
    VarZero : Kind

  data isGood' : Type' Kind -> ℕ -> 𝒰₀ where
    zero : ∀ {k} -> isGood' (kind k) 0
    suc : ∀{k τ} -> isGood' τ n -> isGood' (kind k ⇒ τ) (suc n)

  isGood : Type' Kind -> 𝒰₀
  isGood τ = ∑ isGood' τ
  -- Good = const 𝟙-𝒰
  postulate
    GApp : isGood (kind Te ⇒ (kind Te ⇒ kind Te))
    GLam : isGood ((kind Te ⇒ kind Te) ⇒ kind Te)
    GAll : ∀{τ} -> isGood τ

  data TermCon : (τ : Type' Kind) -> isGood τ → 𝒰₀ where
    App : TermCon (kind Te ⇒ (kind Te ⇒ kind Te)) GApp
    Lam : TermCon ((kind Te ⇒ kind Te) ⇒ kind Te) GLam
    Suc : TermCon (kind Te ⇒ kind Te) GAll
    Zero : TermCon (kind Te) GAll
    Rec-ℕ : TermCon ((kind Te ⇒ kind Te) ⇒ kind Te ⇒ kind Te ⇒ kind Te) GAll

  data isHidden : (𝔧 : MetaJ Kind) -> 𝒰₀ where
    varsuc : ∀{Γ} -> isHidden (Γ ⊢ kind VarSuc ◀ special)
    varzero : ∀{Γ} -> isHidden (Γ ⊢ kind VarZero ◀ special)

  σ : MTC.Signature
  σ = record { MetaKind = Kind ; varsuc = VarSuc ; varzero = VarZero ; isGoodType = isGood ; isHiddenMeta = isHidden ; TermCon = TermCon }

  open MTC.Definitions σ

  TyToTy-⨯ : ℕ -> Type' Kind
  TyToTy-⨯ zero = kind Te
  TyToTy-⨯ (suc n) = kind Te ⇒ TyToTy-⨯ n

  TyToCtx-⨯ : ℕ -> SCtx (Type' Kind)
  TyToCtx-⨯ zero = []
  TyToCtx-⨯ (suc n) = TyToCtx-⨯ n ,, kind Te

  infixl 8 _$$_
  pattern _$$_ a b = app a b




  mutual
    TermFromTerm-⨯-var : ∀{n} -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ var) -> 𝔽ʳ n
    TermFromTerm-⨯-var {zero} (getapp (meta (skip ())))
    TermFromTerm-⨯-var {zero} (getapp (meta (give ())))
    TermFromTerm-⨯-var {suc n} (suc tep te) = suc (TermFromTerm-⨯-var te)
    TermFromTerm-⨯-var {suc n} (zero te) = zero
    TermFromTerm-⨯-var {suc n} (getapp (meta (skip ())))
    TermFromTerm-⨯-var {suc n} (getapp (meta (give ())))

    TermFromTerm-⨯-var-⊥ : ∀{n α β} -> [] ⊩↓ (TyToCtx-⨯ n ⊢ (α ⇒ β) ◀ var) -> 𝟘-𝒰
    TermFromTerm-⨯-var-⊥ {suc n} (suc tep te) = TermFromTerm-⨯-var-⊥ te

    TermFromTerm-⨯-app-⊥ : ∀{n α₁ α₂ α₃ α₄ α₅ β} -> [] ⊩↓-app (TyToCtx-⨯ n ⊢ (α₁ ⇒ α₂ ⇒ α₃ ⇒ α₄ ⇒ α₅ ⇒ β) ◀ main) -> 𝟘-𝒰
    TermFromTerm-⨯-app-⊥ (app te x) = TermFromTerm-⨯-app-⊥ te
    TermFromTerm-⨯-app-⊥ (var te) = TermFromTerm-⨯-var-⊥ te
    TermFromTerm-⨯-app-⊥ (meta (skip ()))
    TermFromTerm-⨯-app-⊥ (meta (give ()))

    TermFromTerm-⨯-app : ∀{n} -> [] ⊩↓-app (TyToCtx-⨯ n ⊢ kind Te ◀ main) -> Λ.Term-λ n
    TermFromTerm-⨯-app (app (app (app (app (app te x₄) x₃) x₂) x₁) x) = 𝟘-rec (TermFromTerm-⨯-app-⊥ te)
    TermFromTerm-⨯-app (app (app (app (app (var te) x₃) x₂) x₁) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
    TermFromTerm-⨯-app (app (app (app (app (meta (skip ())) x₃) x₂) x₁) y)
    TermFromTerm-⨯-app (app (app (app (app (meta (give ())) x₃) x₂) x₁) y)
    TermFromTerm-⨯-app (app (app (app (var te) x₂) x₁) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
    TermFromTerm-⨯-app (app (app (app (con Rec-ℕ) (lam te-suc)) te-zero) te-v) = rec-ℕ (TermFromTerm-⨯ te-suc) (TermFromTerm-⨯ te-zero) (TermFromTerm-⨯ te-v)
    TermFromTerm-⨯-app (app (app (app (meta (skip ())) x₂) x₁) x)
    TermFromTerm-⨯-app (app (app (app (meta (give ())) x₂) x₁) x)
    TermFromTerm-⨯-app (app (app (var te) x₁) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
    TermFromTerm-⨯-app (app (app (con App) x) y) = app (TermFromTerm-⨯ x) (TermFromTerm-⨯ y)
    TermFromTerm-⨯-app (app (app (meta (skip ())) x₁) x)
    TermFromTerm-⨯-app (app (app (meta (give ())) x₁) x)
    TermFromTerm-⨯-app (app (var te) x) = 𝟘-rec $ TermFromTerm-⨯-var-⊥ te
    TermFromTerm-⨯-app (app (con Lam) (lam x)) = lam (TermFromTerm-⨯ x)
    TermFromTerm-⨯-app (app (con Suc) x) = suc (TermFromTerm-⨯ x)
    TermFromTerm-⨯-app (app (meta (skip ())) x)
    TermFromTerm-⨯-app (app (meta (give ())) x)
    TermFromTerm-⨯-app (var x) = var (TermFromTerm-⨯-var x)
    TermFromTerm-⨯-app (con Zero) = zero
    TermFromTerm-⨯-app (meta (skip ()))
    TermFromTerm-⨯-app (meta (give ()))

    TermFromTerm-⨯ : ∀{n} -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ main) -> Λ.Term-λ n
    TermFromTerm-⨯ (getapp x) = TermFromTerm-⨯-app x



  TermToTerm-⨯-var : {n : ℕ} -> 𝔽ʳ n -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ var)
  TermToTerm-⨯-var zero = zero (getapp (meta (skip varzero)))
  TermToTerm-⨯-var (suc i) = suc (getapp (meta (skip varsuc))) (TermToTerm-⨯-var i)

  TermToTerm-⨯ : ∀{n} -> Λ.Term-λ n -> [] ⊩↓ (TyToCtx-⨯ n ⊢ kind Te ◀ main)
  TermToTerm-⨯ (app te te2) = getapp ((con App) $$ (TermToTerm-⨯ te) $$ (TermToTerm-⨯ te2))
  TermToTerm-⨯ (lam te) = getapp ((con Lam) $$ (lam (TermToTerm-⨯ te)))
  TermToTerm-⨯ (var x) = getapp (var (TermToTerm-⨯-var x))
  TermToTerm-⨯ (zero) = getapp (con Zero)
  TermToTerm-⨯ (suc te) = getapp $ (con Suc) $$ (TermToTerm-⨯ te)
  TermToTerm-⨯ (rec-ℕ te-suc te-zero v) = getapp $ con Rec-ℕ $$ (lam (TermToTerm-⨯ te-suc)) $$ TermToTerm-⨯ te-zero $$ TermToTerm-⨯ v

  iso-left-var : ∀{n} -> (i : 𝔽ʳ n) -> TermFromTerm-⨯-var (TermToTerm-⨯-var i) ≡ i
  iso-left-var {.(suc _)} zero = refl
  iso-left-var {.(suc _)} (suc i) = λ k -> suc (iso-left-var i k)

  iso-left : ∀{n} -> (te : Term-λ n) -> TermFromTerm-⨯ (TermToTerm-⨯ te) ≡ te
  iso-left (te $$ te2) = λ i -> iso-left te i $$ iso-left te2 i
  iso-left (lam te) = λ i -> lam (iso-left te i)
  iso-left (var x) = λ k -> var (iso-left-var x k)
  iso-left zero = refl
  iso-left (suc te) = cong suc (iso-left te)
  iso-left (rec-ℕ te te1 te2) = λ i -> rec-ℕ (iso-left te i) (iso-left te1 i) (iso-left te2 i)


  ω : Term-λ 0
  ω = app (lam (app (var zero) (var zero))) (lam (app (var zero) (var zero)))




  -- TermFromTerm-⨯ (MTC.var t) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.var t) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.con Lam) t₁) = lam {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.lam t) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.app t t₂) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.var (MTC.meta ()))
  -- TermFromTerm-⨯ (MTC.app (MTC.var (MTC.meta ())) t₁)
  -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.var t)) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.app (MTC.var t) t₂)) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.app (MTC.lam t) t₂)) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.lam (MTC.app (MTC.app t t₃) t₂)) t₁) = {!!}
  -- TermFromTerm-⨯ (MTC.app (MTC.app t t₂) t₁) = {!!}




