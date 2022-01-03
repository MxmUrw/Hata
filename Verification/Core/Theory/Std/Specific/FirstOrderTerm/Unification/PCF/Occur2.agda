
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Occur2 where

open import Verification.Conventions hiding (Structure)

-- open import Verification.Core.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Misc
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category -- hiding (isSetoid:Function)
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
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)

open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature


-- open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2


module _ {Σ : 𝒯FOSignature 𝑖} where
  mutual
    -- data VarPath-Terms-𝕋× : ∀{Γ Δ} -> (t : Terms-𝕋× Σ Δ Γ) -> {s : Sort Σ} -> (⟨ Γ ⟩ ∍ s) -> 𝒰 𝑖 where
      -- left-Path : ∀{Γ Δ Δ'} -> {t : Terms-𝕋× Σ Δ Γ} -> {t' : Terms-𝕋× Σ Δ' Γ} -> {s : Sort Σ} -> {v : ⟨ Γ ⟩ ∍ s}
      --             -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t ⋆-⧜ t') v

      -- right-Path : ∀{Γ Δ Δ'} -> {t : Terms-𝕋× Σ Δ Γ} -> {t' : Terms-𝕋× Σ Δ' Γ} -> {s : Sort Σ} -> {v : ⟨ Γ ⟩ ∍ s}
      --             -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t' ⋆-⧜ t) v

      -- incl : ∀{Γ τ} -> {t : Term₁-𝕋× Σ Γ τ} -> {s : Sort Σ} -> {v : Γ ∍ s}
      --             -> (p : VarPath-Term-𝕋× t v) -> VarPath-Terms-𝕋× (incl t) v
      -- incl-Path-Terms : {Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× Σ)} {Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× Σ)} (f : 𝑒𝑙 ⟨ Γ ⟩ ⟶ (Term-𝕋× Σ Δ))
      --                   -> ∀{τ} -> (x : ⟨ Γ ⟩ ∍ τ)
      --                   -> ∀{γ} -> (j : ⟨ Δ ⟩ ∍ γ) -> VarPath-Term-𝕋× (f τ x) j
      --                   -> VarPath-Terms-𝕋× (incl-Terms f) j

    -- data VarPath-Terms-𝕋× : ∀{Γ Δ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> (t : Δ ⟶ Γ) -> {s : Sort Σ} -> (⟨ Γ ⟩ ∍ s) -> 𝒰 𝑖 where
    --   left-Path : ∀{Γ Δ Δ' : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> {t : Δ ⟶ Γ} -> {t' : Δ' ⟶ Γ} -> {s : Sort Σ} -> {v : ⟨ Γ ⟩ ∍ s}
    --               -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t ⋆-⧜ t') v

    --   right-Path : ∀{Γ Δ Δ' : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> {t : Δ ⟶ Γ} -> {t' : Δ' ⟶ Γ} -> {s : Sort Σ} -> {v : ⟨ Γ ⟩ ∍ s}
    --               -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t' ⋆-⧜ t) v

    --   incl : ∀{Γ τ} -> {t : Term₁-𝕋× Σ Γ τ} -> {s : Sort Σ} -> {v : Γ ∍ s}
    --               -> (p : VarPath-Term-𝕋× t v) -> VarPath-Terms-𝕋× (incl t) v


    -- data VarPath-Term-𝕋× : ∀{Γ τ} -> (t : Term₁-𝕋× Σ Γ τ) -> {s : Sort Σ} -> (Γ ∍ s) -> 𝒰 𝑖 where
    --   var : ∀{Γ s} -> (x : Γ ∍ s) -> VarPath-Term-𝕋× (var x) x
    --   con : ∀{Γ αs α s} {x : Γ ∍ s} -> (c : Con Σ αs α) -> {ts : 𝑒𝑙 (ι αs) ⟶ (Term-𝕋× Σ (incl (Γ)))}
    --   -- {ts : Terms-𝕋× Σ (incl (ι αs)) (incl Γ) }
    --         -> VarPath-Terms-𝕋× (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl ts)) x
    --         -> VarPath-Term-𝕋× (con c (incl-Terms ts)) x


  private VarPath = VarPath-Term-𝕋×

  mutual
    isFreeVars : ∀{Γ Δ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> (t : (Δ) ⟶ Γ) -> {s : Sort Σ} -> (v : ⟨ Γ ⟩ ∍ s) -> isDecidable (VarPath-Terms-𝕋× t v)
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

    -- isFreeVars (t ⋆-⧜ t₁) v = {!!}
    -- isFreeVars : ∀{Γ Δ} -> (t : Terms-𝕋× Σ (incl Δ) Γ) -> {s : Sort Σ} -> (v : ⟨ Γ ⟩ ∍ s) -> isDecidable (VarPath-Terms-𝕋× t v)
    -- isFreeVars ◌-⧜ v = left λ {()}

    isFreeVar : ∀{Γ τ} -> (t : Term₁-𝕋× Σ Γ τ) -> {s : Sort Σ} -> (v : Γ ∍ s) -> isDecidable (VarPath t v)
    isFreeVar (var x) v with compare-∍ x v
    ... | left x≠v = left λ {(var q) → impossible x≠v}
    ... | just refl-≣-2 = right (var v)
    isFreeVar _ _ = ?
    -- isFreeVar (con c (incl-Terms x)) v with isFreeVars (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl x)) v
    -- ... | left ¬p = left λ {(con c p) → ¬p p}
    -- ... | just  p = right (con c p)

  mutual
    factor-Occurs : ∀{Γ Δ} -> (t : Terms-𝕋× Σ Δ Γ) -> {s : Sort Σ} -> (v : ⟨ Γ ⟩ ∍ s) -> ¬ (VarPath-Terms-𝕋× t v) -> (Terms-𝕋× Σ Δ (incl (⟨ Γ ⟩ \\ v)))
    factor-Occurs ◌-⧜ v ¬occ = ◌-⧜
    factor-Occurs (t ⋆-⧜ s) v ¬occ = factor-Occurs t v (λ occ -> ¬occ (left-Path occ)) ⋆-⧜ factor-Occurs s v (λ occ -> ¬occ (right-Path occ))
    factor-Occurs (incl x) v ¬occ = incl (factor-Occur x v (λ occ -> ¬occ (incl occ)))

    factor-Occur : ∀{Γ τ} -> (t : Term₁-𝕋× Σ Γ τ) -> {s : Sort Σ} -> (v : Γ ∍ s) -> ¬ (VarPath-Term-𝕋× t v) -> (Term₁-𝕋× Σ (Γ \\ v) τ)
    factor-Occur (var x) v occ with compare-∍ x v
    ... | left q        = var (skip-∍ x v q)
    ... | just refl-≣-2 = impossible (occ (var x))
    factor-Occur (con c ts) v ¬occ = con c (factor-Occurs ts v (λ {occ -> ¬occ (con c occ)}))


{-

  module _ {Γ τ} (t : Term₁-𝕋× Σ Γ τ) (v : Γ ∍ τ) (¬occ : ¬ (VarPath-Term-𝕋× t v)) where

    module §-factor where
      mutual
        prop-1s : ∀{Γ Δ τ} (t : Terms-𝕋× Σ Δ Γ) (v : ⟨ Γ ⟩ ∍ τ) (¬occ : ¬ (VarPath-Terms-𝕋× t v))
                 -> ∀{c : 𝐒𝐮𝐛𝐬𝐭 ′(Term-𝕋× Σ)′} -> ∀{h : (ι (incl ⟨ Γ ⟩)) ⟶ c} -> reext-Terms-𝕋× (λ i₁ a → ⟨ h ⟩ i₁ (ι-\\ v i₁ a)) (factor-Occurs t v ¬occ)
                  ≡ reext-Terms-𝕋× ⟨ h ⟩ t
        prop-1s ◌-⧜ v ¬occ {c} {h} = refl-≡
        prop-1s (t ⋆-⧜ s) v ¬occ {c} {h} = λ i → prop-1s t v (λ occ -> ¬occ (left-Path occ)) {h = h} i ⋆-⧜ prop-1s s v (λ occ -> ¬occ (right-Path occ)) {h = h} i
        prop-1s (incl x) v ¬occ {c} {h} = λ i → incl (prop-1 x v (λ occ -> ¬occ (incl occ)) {h = h} i)

        prop-1 : ∀{Γ τ σ} (t : Term₁-𝕋× Σ Γ τ) (v : Γ ∍ σ) (¬occ : ¬ (VarPath-Term-𝕋× t v))
                 -> ∀{c : 𝐒𝐮𝐛𝐬𝐭 ′(Term-𝕋× Σ)′} -> ∀{h : (ι (incl Γ)) ⟶ c} -> reext-Term-𝕋× (λ i₁ a → ⟨ h ⟩ i₁ (ι-\\ v i₁ a)) τ (factor-Occur t v ¬occ)
                  ≡ reext-Term-𝕋× ⟨ h ⟩ τ t
        prop-1 (var x) v ¬occ {c} {h} with compare-∍ x v
        ... | left q = cong (⟨ h ⟩ _) (≡-Str→≡ (§-ι-\\.prop-1 q))
        ... | just refl-≣-2 = impossible (¬occ (var x))
        prop-1 (con c ts) v ¬occ {_} {h} = λ i -> con c (prop-1s ts v (λ occ -> (¬occ (con c occ))) {h = h} i)


    private
      Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)
      Γ' = incl (Γ \\ v)

      t' : Γ' ⊢ τ
      t' = incl $ factor-Occur t v ¬occ

      π' : ι (incl Γ) ⟶ ι (Γ')
      π' = incl (iso-\\ v ◆ ⦗ repure , ⟨ map t' ⟩ ⦘)

      mutual
        lem-4s : ∀{Γ τ Δ} (t : Terms-𝕋× Σ Δ Γ) (v : ⟨ Γ ⟩ ∍ τ) (¬occ : ¬ (VarPath-Terms-𝕋× t v))
                -> (s : ∀ i₁ -> ∀ (p : incl τ ∍ i₁) → Term₁-𝕋× Σ ((⟨ Γ ⟩ \\ v)) i₁)
                -> reext-Terms-𝕋× (λ i₁ a → either (λ x → var x) (s i₁) (iso-\\ v i₁ a)) t ≡ factor-Occurs t v ¬occ
        lem-4s ◌-⧜ v ¬occ s = refl-≡
        lem-4s (t ⋆-⧜ t₁) v ¬occ s = λ i → lem-4s t v (λ occ -> ¬occ (left-Path occ)) s i ⋆-⧜ lem-4s t₁ v (λ occ -> ¬occ (right-Path occ)) s i
        lem-4s (incl x) v ¬occ s = λ i -> incl (lem-4 x v (λ occ -> ¬occ (incl occ)) s i)

        lem-4 : ∀{Γ τ σ} (t : Term₁-𝕋× Σ Γ σ) (v : Γ ∍ τ) (¬occ : ¬ (VarPath-Term-𝕋× t v))
                -> (s : ∀ i₁ -> ∀ (p : incl τ ∍ i₁) → Term₁-𝕋× Σ (Γ \\ v) i₁)
                -> reext-Term-𝕋× (λ i₁ a → either (λ x → var x) (s i₁) (iso-\\ v i₁ a)) σ t ≡ factor-Occur t v ¬occ
        lem-4 (var x) v ¬occ s with compare-∍ x v
        ... | left x₁ = refl-≡
        ... | just refl-≣-2 = impossible (¬occ (var x))
        lem-4 (con c ts) v ¬occ s = λ i -> con c (lem-4s ts v (λ occ -> (¬occ (con c occ))) s i)

      lem-5 : ∀ (i : Sort Σ) (x : incl τ ∍ i) -> ⟨ (map (incl t)) ◆ π' ⟩ i x ≡ ⟨ (map (simpleVar v)) ◆ π' ⟩ i x
      lem-5 i incl = P
        where
          Q : either (λ x → var x) (⟨ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 t' ⟩ i) (iso-\\ v i v) ≡ factor-Occur t v ¬occ
          Q = cong (either (λ x → var x) (⟨ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 t' ⟩ i)) (§-iso-\\.prop-1 v)

          P : reext-Term-𝕋×
                (λ i₁ a → either (λ x → var x) ((⟨ map t' ⟩) i₁) -- (λ { a incl → factor-Occur t v ¬occ })
                                 (iso-\\ v i₁ a))
                i t
                ≡
                either (λ x → var x) ((⟨ map t' ⟩) i)
                       (iso-\\ v i v)
          P = trans-Path (lem-4 t v ¬occ _) (sym-Path Q)

      equate-π' : (map (incl t)) ◆ π' ∼ (map (simpleVar v)) ◆ π'
      equate-π' = incl (λ i → funExt (lem-5 i))


      compute-Coeq' : ∀{c : 𝐒𝐮𝐛𝐬𝐭 _} -> (h : ι (incl Γ) ⟶ c) -> (map (incl t) ◆ h) ∼ (map (simpleVar v) ◆ h) -> ∑ λ (ξ : ι Γ' ⟶ c) -> (π' ◆ ξ ∼ h)
      compute-Coeq' {c} h p = ξ , P
        where
          ξ : ι Γ' ⟶ c
          ξ = incl (ι-\\ v ◆ ⟨ h ⟩)

          P-9 : ∀ i -> (x : Γ ∍ i) →
                reext-Term-𝕋× (λ i₁ a → ⟨ h ⟩ i₁ (ι-\\ v i₁ a)) i
                (either var ((⟨ map t' ⟩) i)
                (iso-\\ v i x))
                ≡ ⟨ h ⟩ i x
          P-9 i x with compare-∍ x v
          ... | left x≠v = cong (⟨ h ⟩ i) (≡-Str→≡ (§-ι-\\.prop-1 x≠v))
          ... | just (refl-≣ , refl-≣) =
            let Q-1 : reext-Term-𝕋× ⟨ h ⟩ i t ≡ ⟨ h ⟩ i x
                Q-1 = funExt⁻¹ (⟨ p ⟩ i) incl
            in trans-Path (§-factor.prop-1 t v ¬occ) (Q-1)

          P : π' ◆ ξ ∼ h
          P = incl (λ i → funExt (P-9 i))

      ι' : ι Γ' ⟶ ι (incl Γ)
      ι' = incl (ι-\\ v ◆ repure)


      lem-6 : ι' ◆ π' ∼ id
      lem-6 = incl (λ i -> funExt (P i))
        where
          P : ∀ i x -> ⟨ ι' ◆ π' ⟩ i x ≡ var x
          P i x with compare-∍ (ι-\\ v i x) v
          ... | left q = cong var (≡-Str→≡ (§-ι-\\.prop-2 q))
          ... | just (refl-≣ , q) = impossible (§-ι-\\.prop-3 q)

    P-11 : ∀{x : 𝐒𝐮𝐛𝐬𝐭 (Terms Σ)} -> {α β : ι Γ' ⟶ x} -> (π' ◆ α ∼ π' ◆ β) -> α ∼ β
    P-11 {x} {α} {β} p = p
        ⟪ (_◈_ {f = ι'} {g = ι'} {h = π' ◆ α} {i = π' ◆ β} refl) ⟫
        >> ι' ◆ (π' ◆ α) ∼ ι' ◆ (π' ◆ β) <<
        ⟪ assoc-r-◆ {f = ι'} {g = π'} {h = α} ≀∼≀ assoc-r-◆ {f = ι'} {g = π'} {h = β} ⟫
        >> (ι' ◆ π') ◆ α ∼ (ι' ◆ π') ◆ β <<
        ⟪ lem-6 ◈ refl ≀∼≀ lem-6 ◈ refl ⟫
        >> id ◆ α ∼ id ◆ β <<
        ⟪ unit-l-◆ ≀∼≀ unit-l-◆ ⟫

    isEpi:π' : isEpi π'
    isEpi:π' = epi P-11

    isCoequalizer:byNoOccur : isCoequalizer (map (incl t)) (map (simpleVar v)) (ι (Γ'))
    isCoequalizer.π₌ isCoequalizer:byNoOccur = π'
    isCoequalizer.equate-π₌ isCoequalizer:byNoOccur = equate-π'
    isCoequalizer.compute-Coeq isCoequalizer:byNoOccur = compute-Coeq'
    isCoequalizer.isEpi:π₌ isCoequalizer:byNoOccur = isEpi:π'

    hasCoequalizer:byNoOccur : hasCoequalizer (incl t) (simpleVar v)
    hasCoequalizer:byNoOccur = Γ' since (isCoequalizer:byFullyFaithfull isCoequalizer:byNoOccur)

-}

