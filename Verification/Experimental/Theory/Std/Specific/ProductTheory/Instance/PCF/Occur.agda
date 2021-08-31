
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Occur where

open import Verification.Conventions hiding (Structure)

-- open import Verification.Experimental.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything -- hiding (isSetoid:Function)
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory -- hiding (isSetoid:Function)
open import Verification.Experimental.Data.Product.Definition

-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Property.Base
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Reflection
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder 
open import Verification.Experimental.Order.Lattice hiding (⊥)

open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.List.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.FiniteIndexed.Property.Merge

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2


module _ {𝑨 : 𝕋× 𝑖} where
  mutual
    data VarPath-Terms-𝕋× : ∀{Γ Δ} -> (t : Terms-𝕋× 𝑨 Δ Γ) -> {s : Sort 𝑨} -> (⟨ Γ ⟩ ∍ s) -> 𝒰 𝑖 where
      left-Path : ∀{Γ Δ Δ'} -> {t : Terms-𝕋× 𝑨 Δ Γ} -> {t' : Terms-𝕋× 𝑨 Δ' Γ} -> {s : Sort 𝑨} -> {v : ⟨ Γ ⟩ ∍ s}
                  -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t ⋆-⧜ t') v

      right-Path : ∀{Γ Δ Δ'} -> {t : Terms-𝕋× 𝑨 Δ Γ} -> {t' : Terms-𝕋× 𝑨 Δ' Γ} -> {s : Sort 𝑨} -> {v : ⟨ Γ ⟩ ∍ s}
                  -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t' ⋆-⧜ t) v

      incl : ∀{Γ τ} -> {t : Term₁-𝕋× 𝑨 Γ τ} -> {s : Sort 𝑨} -> {v : Γ ∍ s}
                  -> (p : VarPath-Term-𝕋× t v) -> VarPath-Terms-𝕋× (incl t) v

    data VarPath-Term-𝕋× : ∀{Γ τ} -> (t : Term₁-𝕋× 𝑨 Γ τ) -> {s : Sort 𝑨} -> (Γ ∍ s) -> 𝒰 𝑖 where
      var : ∀{Γ s} -> (x : Γ ∍ s) -> VarPath-Term-𝕋× (var x) x
      con : ∀{Γ αs α s} {x : Γ ∍ s} -> (c : Con 𝑨 αs α) -> {ts : Terms-𝕋× 𝑨 (incl (ι αs)) (incl Γ) }
            -> VarPath-Terms-𝕋× ts x
            -> VarPath-Term-𝕋× (con c ts) x

  private VarPath = VarPath-Term-𝕋×

  mutual
    isFreeVars : ∀{Γ Δ} -> (t : Terms-𝕋× 𝑨 Δ Γ) -> {s : Type 𝑨} -> (v : ⟨ Γ ⟩ ∍ s) -> isDecidable (VarPath-Terms-𝕋× t v)
    isFreeVars ◌-⧜ v = left λ {()}
    isFreeVars (t ⋆-⧜ s) v with isFreeVars t v | isFreeVars s v
    ... | left ¬l | left ¬r = left λ {(left-Path l) → ¬l l
                                    ;(right-Path r) -> ¬r r
                                    }
    ... | left ¬l | just r  = right (right-Path r)
    ... | just l  | _       = right (left-Path l)
    isFreeVars (incl x) v with isFreeVar x v
    ... | left q = left λ {(incl p) → q p}
    ... | just q = right (incl q)

    isFreeVar : ∀{Γ τ} -> (t : Term₁-𝕋× 𝑨 Γ τ) -> {s : Type 𝑨} -> (v : Γ ∍ s) -> isDecidable (VarPath t v)
    isFreeVar (var x) v with compare-∍ x v
    ... | left x≠v = left λ {(var q) → impossible x≠v}
    ... | just refl-=-∍ = right (var v)
    isFreeVar (con c x) v with isFreeVars x v
    ... | left ¬p = left λ {(con c p) → ¬p p}
    ... | just  p = right (con c p)

  mutual
    factor-Occurs : ∀{Γ Δ} -> (t : Terms-𝕋× 𝑨 Δ Γ) -> {s : Type 𝑨} -> (v : ⟨ Γ ⟩ ∍ s) -> ¬ (VarPath-Terms-𝕋× t v) -> (Terms-𝕋× 𝑨 Δ (incl (⟨ Γ ⟩ \\ v)))
    factor-Occurs ◌-⧜ v ¬occ = ◌-⧜
    factor-Occurs (t ⋆-⧜ s) v ¬occ = factor-Occurs t v (λ occ -> ¬occ (left-Path occ)) ⋆-⧜ factor-Occurs s v (λ occ -> ¬occ (right-Path occ))
    factor-Occurs (incl x) v ¬occ = incl (factor-Occur x v (λ occ -> ¬occ (incl occ)))

    factor-Occur : ∀{Γ τ} -> (t : Term₁-𝕋× 𝑨 Γ τ) -> {s : Type 𝑨} -> (v : Γ ∍ s) -> ¬ (VarPath-Term-𝕋× t v) -> (Term₁-𝕋× 𝑨 (Γ \\ v) τ)
    factor-Occur (var x) v occ with compare-∍ x v
    ... | left q        = var (skip-∍ x v q)
    ... | just refl-=-∍ = impossible (occ (var x))
    factor-Occur (con c ts) v ¬occ = con c (factor-Occurs ts v (λ {occ -> ¬occ (con c occ)}))


  module _ {Γ τ} (t : Term₁-𝕋× 𝑨 Γ τ) (v : Γ ∍ τ) (¬occ : ¬ (VarPath-Term-𝕋× t v)) where
    private
      Γ' : 𝐂𝐭𝐱 𝑨
      Γ' = incl (Γ \\ v)

      t' : Γ' ⊢ τ
      t' = incl $ factor-Occur t v ¬occ

      π' : ι (incl Γ) ⟶ ι (Γ')
      π' = incl (iso-\\ v ◆ ⦗ repure , ⟨ map t' ⟩ ⦘)

      lem-4 : ∀{Γ τ} (t : Term₁-𝕋× 𝑨 Γ τ) (v : Γ ∍ τ) (¬occ : ¬ (VarPath-Term-𝕋× t v))
              -> (s : ∀ i₁ -> ∀ (p : incl τ ∍ i₁) → Term₁-𝕋× 𝑨 (Γ \\ v) i₁)
              -> reext-Term-𝕋× (λ i₁ a → either (λ x → var x) (s i₁) (iso-\\ v i₁ a)) τ t ≡ factor-Occur t v ¬occ
      lem-4 (var x) v ¬occ s with compare-∍ x v
      ... | left x₁ = refl-≡
      ... | just q with isProp-=-∍ q refl-=-∍
      ... | X = {!!}
      lem-4 (con c x) v ¬occ s = {!!}

    --   lem-5 : ∀ (i : Type 𝑨) (x : incl τ ∍ i) -> ⟨ (map (incl t)) ◆ π' ⟩ i x ≡ ⟨ (map (simpleVar v)) ◆ π' ⟩ i x
    --   lem-5 i incl = P
    --     where
    --       P : reext-Term-𝕋×
    --             (λ i₁ a → either (λ x → var x) ((⟨ map t' ⟩) i₁) -- (λ { a incl → factor-Occur t v ¬occ })
    --                              (iso-\\ v i₁ a))
    --             i t
    --             ≡
    --             either (λ x → var x) ((⟨ map t' ⟩) i)
    --                    (iso-\\ v i v)
    --       P = {!!}

    --   equate-π' : (map (incl t)) ◆ π' ∼ (map (simpleVar v)) ◆ π'
    --   equate-π' = incl (λ i → funExt (lem-5 i))



    -- isCoequalizer:byNoOccur : isCoequalizer (map (incl t)) (map (simpleVar v)) (ι (Γ'))
    -- isCoequalizer.π₌ isCoequalizer:byNoOccur = π'
    -- isCoequalizer.equate-π₌ isCoequalizer:byNoOccur = equate-π'
    -- isCoequalizer.compute-Coeq isCoequalizer:byNoOccur = {!!}
    -- isCoequalizer.isEpi:π₌ isCoequalizer:byNoOccur = {!!}

    -- hasCoequalizer:byNoOccur : hasCoequalizer (incl t) (simpleVar v)
    -- hasCoequalizer:byNoOccur = Γ' since (isCoequalizer:byFullyFaithfull isCoequalizer:byNoOccur)





