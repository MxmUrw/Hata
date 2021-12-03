
module Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.PCF.OccurFail where

open import Verification.Conventions hiding (Structure ; ℕ)

-- open import Verification.Core.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Algebra.Monoid.Notation.Associativity
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Everything -- hiding (isSetoid:Function)
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory -- hiding (isSetoid:Function)
open import Verification.Core.Data.Product.Definition

-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Property.Base
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Reflection
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Preservation
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice hiding (⊥)

open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.List.Variant.Base.Definition
-- open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.FormalSystem

open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.PCF.Occur


-- TODO: abstract these statements into general structures on orders
infixl 15 _⩚⋆⩚_
_⩚⋆⩚_ : ∀{a b c d : 人ℕ} -> (a ≤ b) -> (c ≤ d) -> a ⋆ c ≤ b ⋆ d
_⩚⋆⩚_ p q = {!!}

diag-⋆-≤ : ∀{a : 人ℕ} -> a ≤ a ⋆ a
diag-⋆-≤ = {!!}

initial-◌-≤ : ∀{a : 人ℕ} -> ◌ ≤ a
initial-◌-≤ = {!!}

cancel-⋆-≤-right : ∀{a b c : 人ℕ} -> a ⋆ c ≤ b ⋆ c -> a ≤ b
cancel-⋆-≤-right = {!!}

module _ {X : 𝒰 𝑖} {{_ : isSetoid {𝑗} X}} where
  fromPath : ∀{a b : X} -> a ≡ b -> a ∼ b
  fromPath {a = a} p = transport (λ i -> a ∼ p i) refl

instance
  isContradiction:1≤0 : ∀{a : 人ℕ} -> isContradiction (1 ⋆ a ≤ 0)
  isContradiction:1≤0 = {!!}

module _ {𝑨 : 𝕋× 𝑖} where

  mutual
    depths-𝕋× : ∀{Γ Δ} -> (t : Terms-𝕋× 𝑨 Δ Γ) -> 人ℕ
    depths-𝕋× ◌-⧜ = 0
    depths-𝕋× (t ⋆-⧜ s) = depths-𝕋× t ⋆ depths-𝕋× s
    depths-𝕋× (incl x) = depth-𝕋× x

    depth-𝕋× : ∀{Γ τ} -> (t : Term₁-𝕋× 𝑨 Γ τ) -> 人ℕ
    depth-𝕋× (var x) = 0
    depth-𝕋× (con c x) = 1 ⋆ (depths-𝕋× x)

  module §-depth-𝕋× where
    mutual
      prop-1s : ∀{Γ Δ} (t : Terms-𝕋× 𝑨 Δ Γ) -> ∀{Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} -> (σ : ι (incl ⟨ Γ ⟩) ⟶ ι Γ')
              -> (depths-𝕋× t) ≤ (depths-𝕋× (reext-Terms-𝕋× ⟨ σ ⟩ t))
      prop-1s ◌-⧜ σ = reflexive
      prop-1s (t ⋆-⧜ s) σ = prop-1s t σ ⩚⋆⩚ prop-1s s σ
      prop-1s (incl x) σ = prop-1 x σ

      prop-1 : ∀{Γ τ} (t : Term₁-𝕋× 𝑨 Γ τ) -> ∀{Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} -> (σ : ι (incl Γ) ⟶ ι Γ')
              -> (depth-𝕋× t) ≤ (depth-𝕋× (reext-Term-𝕋× ⟨ σ ⟩ _ t))
      prop-1 (var x) σ = initial-◌-≤
      prop-1 (con c x) σ = reflexive ⩚⋆⩚ prop-1s x σ

    mutual
      prop-2s : ∀{Γ Δ τ'} (t : Terms-𝕋× 𝑨 Δ Γ) (v : ⟨ Γ ⟩ ∍ τ') (occ : (VarPath-Terms-𝕋× t v)) -> ∀{Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} -> (σ : ι (incl ⟨ Γ ⟩) ⟶ ι Γ')
              -> (depths-𝕋× t) ⋆ (depth-𝕋× (⟨ σ ⟩ _ v)) ≤ (depths-𝕋× (reext-Terms-𝕋× ⟨ σ ⟩ t))
      prop-2s (t ⋆-⧜ s) v (left-Path occ) σ = P
        where
          #t = depths-𝕋× t
          #s = depths-𝕋× s
          #v = depth-𝕋× (⟨ σ ⟩ _ v)
          P = #t ⋆ #s ⋆ #v         ⟨ 命reflexive (assoc-l-⋆ ∙ (refl ≀⋆≀ comm-⋆) ∙ assoc-r-⋆) ⟩-≤
              #t ⋆ #v ⋆ #s         ⟨ prop-2s t v occ σ ⩚⋆⩚ prop-1s s σ ⟩-≤
              _ ⋆ _                ∎-≤

      prop-2s (t ⋆-⧜ s) v (right-Path occ) σ = P
        where
          #t = depths-𝕋× t
          #s = depths-𝕋× s
          #v = depth-𝕋× (⟨ σ ⟩ _ v)
          P = #t ⋆ #s ⋆ #v         ⟨ 命reflexive assoc-l-⋆ ⟩-≤
              #t ⋆ (#s ⋆ #v)       ⟨ prop-1s t σ ⩚⋆⩚ prop-2s s v occ σ ⟩-≤
              _ ⋆ _                ∎-≤

      prop-2s (incl x) v (incl occ) σ = prop-2 x v occ σ

      prop-2 : ∀{Γ τ τ'} (t : Term₁-𝕋× 𝑨 Γ τ) (v : Γ ∍ τ') (occ : (VarPath-Term-𝕋× t v)) -> ∀{Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} -> (σ : ι (incl Γ) ⟶ ι Γ')
              -> (depth-𝕋× t) ⋆ (depth-𝕋× (⟨ σ ⟩ _ v)) ≤ (depth-𝕋× (reext-Term-𝕋× ⟨ σ ⟩ _ t))
      prop-2 (var x) .x (var .x) σ = 命reflexive (unit-l-⋆)
      prop-2 (con c ts) v (con _ occ) σ = 命reflexive (assoc-l-⋆) ⟡ monotone-l-⋆-人ℕ (prop-2s ts v occ σ)


  module _ {Γ τ} (t : Term₁-𝕋× 𝑨 Γ τ) (v : Γ ∍ τ) (occ : (VarPath-Term-𝕋× t v)) {d} (pd : depth-𝕋× t ∼ 1 ⋆ d) where
    -- module _ {σ : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} {{_ : isCoequalizer (incl t) (simpleVar v) σ}} where

    module §-Occur-𝕋× {Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} {{_ : isCoequalizerCandidate (map (⧜subst (incl t))) (map (simpleVar v)) (ι Γ')}} where

      private
        σ : ι (incl Γ) ⟶ ι Γ'
        σ = π₌?

        val : Term₁-𝕋× 𝑨 ⟨ Γ' ⟩ τ
        val = ⟨ σ ⟩ _ v

        lem-1 : reext-Term-𝕋× ⟨ σ ⟩ _ t ≡ val
        lem-1 = (funExt⁻¹ (⟨ equate-π₌? ⟩ _)) incl

        lem-2 : depth-𝕋× (reext-Term-𝕋× ⟨ σ ⟩ _ t) ≡ depth-𝕋× val
        lem-2 = cong depth-𝕋× lem-1

        lem-3 : depth-𝕋× t ⋆ depth-𝕋× val ≤ depth-𝕋× (reext-Term-𝕋× ⟨ σ ⟩ _ t)
        lem-3 = §-depth-𝕋×.prop-2 t v occ σ

        lem-4 : (1 ⋆ d) ⋆ depth-𝕋× val ≤ 0 ⋆ depth-𝕋× val
        lem-4 = (1 ⋆ d) ⋆ depth-𝕋× val             ⟨ 命reflexive (pd ⁻¹) ⩚⋆⩚ reflexive ⟩-≤
                depth-𝕋× t ⋆ depth-𝕋× val          ⟨ lem-3 ⟩-≤
                depth-𝕋× (reext-Term-𝕋× ⟨ σ ⟩ _ t)  ⟨ 命reflexive (fromPath lem-2) ⟩-≤
                depth-𝕋× val                       ⟨ 命reflexive (unit-l-⋆ ⁻¹) ⟩-≤
                0 ⋆ depth-𝕋× val                    ∎-≤

        lem-5 : (1 ⋆ d) ≤ 0
        lem-5 = cancel-⋆-≤-right lem-4

      prop-1 : 𝟘-𝒰
      prop-1 = impossible lem-5

    hasNoCoequalizerCandidate:byOccur : ¬ hasCoequalizerCandidate (⧜subst (incl t) , simpleVar v)
    hasNoCoequalizerCandidate:byOccur P = §-Occur-𝕋×.prop-1 {Γ' = Γ'}
      where
        Γ' = ⟨ P ⟩

        instance
          P' : isCoequalizerCandidate (map (⧜subst (incl t))) (map (simpleVar v)) (ι Γ')
          P' = isCoequalizerCandidate:byEquivalence (of P)



