
module Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Instance.HasBoundary where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.FinR.Definition

open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Substitution.Normal.Definition

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Definition
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Module
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Instance.FormalSystem
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Instance.PCF
open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition

open import Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary
open import Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Definition

open import Verification.Experimental.Theory.Std.Presentation.CheckTree.Definition2
open import Verification.Experimental.Theory.Std.Presentation.CheckTree.FromUnification
open import Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Instance.IsCheckingBoundary

-- for anvectree
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromANVecTree
  -- using (ANVecTree)


data Node : 𝒰₀ where
  zeroᵗ sucᵗ : Node

  varᵗ appᵗ lamᵗ : Node

  sletᵗ : Node

Fin→∍ : ∀{as : List 𝒷₀} -> (i : Fin-R (length as)) -> (ι as) ∍ (lookup' as i)
Fin→∍ {x ∷ as} zero = left-∍ incl
Fin→∍ {x ∷ as} (suc i) = right-∍ (Fin→∍ i)

lvar : ∀{as : List 𝒷₀} -> (i : Fin-R (length as)) -> Term₁-𝕋× 𝒷 ((ι as)) (lookup' as i)
lvar x = var (Fin→∍ x)


private
  size : Node -> ℕ
  size zeroᵗ = 0
  size sucᵗ = 1
  size varᵗ = 1
  size appᵗ = 2
  size lamᵗ = 1
  size sletᵗ = 2

  initbΛ : Node → ℬ
  initbΛ zeroᵗ = incl (全tyᵗ ∷ 分tyᵗ ∷ [])
  initbΛ sucᵗ = incl (全tyᵗ ∷ 分tyᵗ ∷ 分tyᵗ ∷ [])
  initbΛ varᵗ = incl (全tyᵗ ∷ 分tyᵗ ∷ [])
  initbΛ appᵗ = incl (全tyᵗ ∷ 分tyᵗ ∷ 分tyᵗ ∷ [])
  initbΛ lamᵗ = incl (全tyᵗ ∷ 分tyᵗ ∷ 分tyᵗ ∷ [])
  initbΛ sletᵗ = incl (全tyᵗ ∷ 分tyᵗ ∷ 分tyᵗ ∷ [])

  initvΛ : (a : Node) → HomFᵘ (incl (jdgᵗ ∷ [])) (initbΛ a)
  initvΛ zeroᵗ = ♮subst (((lvar 0 ▻ lvar 1) 影⊢ lvar 1) ∷ [])
  initvΛ sucᵗ = ♮subst ((lvar 0 ▻ lvar 2) 影⊢ lvar 1 ∷ [])
  initvΛ varᵗ = ♮subst ((lvar 0 分⊢ lvar 1) ∷ [])
  initvΛ appᵗ = ♮subst ((lvar 0 分⊢ lvar 2) ∷ [])
  initvΛ lamᵗ = ♮subst ((lvar 0 分⊢ (lvar 1 ⇒ lvar 2)) ∷ [])
  initvΛ sletᵗ = ♮subst ((lvar 0 分⊢ lvar 2) ∷ [])

  initvsΛ : (a : Node) → Vec (HomFᵘ (incl (jdgᵗ ∷ ⦋⦌)) (initbΛ a)) (size a)
  initvsΛ zeroᵗ = ⦋⦌
  initvsΛ sucᵗ = (♮subst ((lvar 0 影⊢ lvar 1) ∷ [])) ∷ ⦋⦌
  initvsΛ varᵗ = (♮subst ((lvar 0 影⊢ lvar 1) ∷ [])) ∷ ⦋⦌
  initvsΛ appᵗ = ♮subst ((lvar 0 分⊢ (lvar 1 ⇒ lvar 2)) ∷ []) ∷ ♮subst ((lvar 0 分⊢ lvar 1) ∷ []) ∷ ⦋⦌
  initvsΛ lamᵗ = (♮subst (((lvar 0 ▻ lvar 1) 分⊢ lvar 2) ∷ [])) ∷ ⦋⦌
  initvsΛ sletᵗ = (♮subst ((lvar 0 分⊢ lvar 1) ∷ [])) ∷ ((♮subst (((lvar 0 ▻ lvar 1) 分⊢ lvar 2) ∷ [])) ∷ ⦋⦌)

  data WellTypedΛ {b : ℬ} : (a : Node) → HomFᵘ (incl (jdgᵗ ∷ ⦋⦌)) b
                  → Vec (HomFᵘ (incl (jdgᵗ ∷ ⦋⦌)) b) (size a) → 𝒰₀ where
    typeZero : ∀{Γ α} -> WellTypedΛ zeroᵗ (♮subst (((Γ ▻ α) 影⊢ α) ∷ [])) ⦋⦌
    typeSuc : ∀{Γ α β} -> WellTypedΛ sucᵗ (♮subst (((Γ ▻ β) 影⊢ α) ∷ [])) ((♮subst ((Γ 影⊢ α) ∷ [])) ∷ ⦋⦌)
    typeVar : ∀{Γ α} -> WellTypedΛ varᵗ (♮subst ((Γ 分⊢ α) ∷ [])) ((♮subst ((Γ 影⊢ α) ∷ [])) ∷ ⦋⦌)
    typeApp : ∀{Γ α β} -> WellTypedΛ appᵗ (♮subst ((Γ 分⊢ β) ∷ []))
                                          ((♮subst ((Γ 分⊢ (α ⇒ β)) ∷ []))
                                          ∷ ((♮subst ((Γ 分⊢ α) ∷ [])) ∷ ⦋⦌))
    typeLam : ∀{Γ α β} -> WellTypedΛ lamᵗ (♮subst ((Γ 分⊢ (α ⇒ β)) ∷ [])) ((♮subst (((Γ ▻ α) 分⊢ β) ∷ [])) ∷ ⦋⦌)
    typeSlet : ∀{Γ α β} -> WellTypedΛ sletᵗ (♮subst ((Γ 分⊢ β) ∷ []))
                                            ((♮subst ((Γ 分⊢ α) ∷ []))
                                            ∷ (♮subst (((Γ ▻ α) 分⊢ β) ∷ []))
                                            ∷ ⦋⦌)
  initwtΛ : {a : Node} → WellTypedΛ a (initvΛ a) (initvsΛ a)
  initwtΛ {zeroᵗ} = typeZero
  initwtΛ {sucᵗ} = typeSuc
  initwtΛ {varᵗ} = typeVar
  initwtΛ {appᵗ} = typeApp
  initwtΛ {lamᵗ} = typeLam
  initwtΛ {sletᵗ} = typeSlet

  map-WTΛ : {b x : ♮𝐂𝐭𝐱ᵘ 𝒷} {a : Node} {v0 : HomFᵘ (incl (jdgᵗ ∷ ⦋⦌)) b}
            {vs : Vec (HomFᵘ (incl (jdgᵗ ∷ ⦋⦌)) b) (size a)} (ϕ : b ⟶ x) →
            WellTypedΛ a v0 vs →
            WellTypedΛ a (v0 ◆-♮𝐒𝐮𝐛𝐬𝐭 ϕ) (map-Vec (λ g → g ◆-♮𝐒𝐮𝐛𝐬𝐭 ϕ) vs)
  map-WTΛ ϕ typeZero = typeZero
  map-WTΛ ϕ typeSuc = typeSuc
  map-WTΛ ϕ typeVar = typeVar
  map-WTΛ ϕ typeApp = typeApp
  map-WTΛ ϕ typeLam = typeLam
  map-WTΛ ϕ typeSlet = typeSlet

instance
  hasBoundary:Λ : hasBoundary ℬ (HomF (incl (jdgᵗ ∷ []))) (Node) (size)
  hasBoundary:Λ = record
                    { initb = initbΛ
                    ; initv = initvΛ
                    ; initvs = initvsΛ
                    ; WT = WellTypedΛ
                    ; initwt = initwtΛ
                    ; map-WT = map-WTΛ
                    }

instance
  isSet-Str:ℬΛ : isSet-Str ℬ
  isSet-Str:ℬΛ = {!!}

constructTerm-Λ : ∀{μ α}
                -> ANVecTree _ _ (ℬ) (HomF (incl (jdgᵗ ∷ []))) (μ) (♮subst (α ∷ []))
                -> Term (α)
constructTerm-Λ (ANVecTree.node1 zeroᵗ _ _ typeZero x₁) = zero
constructTerm-Λ (ANVecTree.node1 sucᵗ _ _ typeSuc (x ∷ x₁)) = suc (constructTerm-Λ x)
constructTerm-Λ (node1 varᵗ _ _ typeVar (x ∷ x₁)) = var (constructTerm-Λ x)
constructTerm-Λ (node1 appᵗ _ _ typeApp (x ∷ (x₁ ∷ x₂))) = app (constructTerm-Λ x) (constructTerm-Λ x₁)
constructTerm-Λ (node1 lamᵗ _ _ typeLam (x ∷ x₁)) = lam (constructTerm-Λ x)
constructTerm-Λ (node1 sletᵗ _ _ typeSlet (x ∷ (x₁ ∷ x₂))) = slet (constructTerm-Λ x) (constructTerm-Λ x₁)



