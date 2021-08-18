
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.SuccessRigidRigid where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Morphism
-- open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
-- open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Universe.Everything hiding (isCategory:𝒰)
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.List.Definition
open import Verification.Experimental.Data.Nat.Free
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple

open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
-- open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Category.Std.Functor.RelativeAdjoint

open import Verification.Experimental.Data.Indexed.Definition
-- open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.FiniteIndexed.Property.Adjunction
-- open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Substitution.Definition
-- open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
-- open import Verification.Experimental.Category.Std.Category.Subcategory.Full

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteCoproductCategory

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder 
open import Verification.Experimental.Order.Lattice hiding (⊥)
open import Verification.Experimental.Computation.Unification.Definition
-- open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Experimental.Computation.Unification.Monoidic.ToCoequalizer
-- open import Verification.Experimental.Algebra.Monoid.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
-- open import Verification.Experimental.Algebra.MonoidAction.Definition

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.Base



module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where




  ----------------------------------------------------------
  -- the var/var case

  success-var-var : ∀{Γ Δ : List (Jdg₂ ⟨ K ⟩)} {α : ⟨ K ⟩} {j : 𝐏𝐚𝐭 K}
            -> (x : ι Γ ∍ (Δ ⇒ α))    -> (ts : Pat-pats ⟨ j ⟩ Γ (ι Δ))
                                        -> (ts' : Pat-pats ⟨ j ⟩ Γ (ι Δ))
            -> isSplittableC (𝐏𝐚𝐭 K) 1 (incl (app-var x ts) , incl (app-var x ts')) (SplitP)
  success-var-var {Γ} {Δ} {α} {𝔍} (vx) (lam tsx) (lam tsy) = {!!} {-
    where

      -- TODO: in the following, `surj` does not work, have to use `surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭` instead. (even though in another file it worked)
      mfam : 1 ∍ tt -> _
      mfam _ = incl (γₗ! Γ (ι Δ)) , surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsx)) , surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsy))


      lem-1 : ∀{x} (σ : 𝔍 ⟶ x) -> (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var vx (lam tsx))) ≣ incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var vx (lam tsy))))
                                    -> (∀ (p : 1 ∍ tt) -> surj (incl (refree-pats tsx)) ◆ σ ≣ surj (incl (refree-pats tsy)) ◆ σ)
      lem-1 σ p _ = p
                      ⟪ cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 ⟫
                      ⟪ cancel-injective-app-var' ⟫
                      ⟪ cancel-injective-lam ⟫

                      >> (∀ i -> tsx i ◆ reext ⟨ map σ ⟩ (γₗ Γ i) ≡ tsy i ◆ reext ⟨ map σ ⟩ (γₗ Γ i)) <<

                      ⟪ construct-precomp-free {f₀ = tsx} {f₁ = tsy} {g₀ = reext ⟨ map σ ⟩} {g₁ = reext ⟨ map σ ⟩} ⟫

                      >> (∀ i -> ((refree-pats tsx i)) ◆ reext ⟨ map σ ⟩ i ≡ ((refree-pats tsy i)) ◆ reext ⟨ map σ ⟩ i) <<

                      ⟪ incl ⟫

                      >> (incl (refree-pats tsx)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ ∼ (incl (refree-pats tsy)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ <<

                      ⟪ (sym (inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsx)})) ◈ refl ≀∼≀
                        (sym (inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsy)})) ◈ refl ⟫

                      >> map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsx))) ◆-𝐑𝐞𝐊𝐥𝐬 map σ ∼ map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsy))) ◆-𝐑𝐞𝐊𝐥𝐬 map σ <<

                      ⟪ functoriality-◆ {f = surj (incl (refree-pats tsx))} {g = σ} ⁻¹ ≀∼≀ functoriality-◆ {f = surj (incl (refree-pats tsy))} {g = σ} ⁻¹ ⟫

                      >> map (surj (incl (refree-pats tsx)) ◆ σ) ∼ map (surj (incl (refree-pats tsy)) ◆ σ) <<
                      ⟪ cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 ⟫
                      >> surj (incl (refree-pats tsx)) ◆ σ ∼ surj (incl (refree-pats tsy)) ◆ σ <<

      lem-2 : ∀{x} (σ : 𝔍 ⟶ x) -> (∀ (p : 1 ∍ tt) -> surj (incl (refree-pats tsx)) ◆ σ ≣ surj (incl (refree-pats tsy)) ◆ σ)
                                  -> (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var vx (lam tsx))) ≣ incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var vx (lam tsy))))
      lem-2 σ p = p (left-∍ incl)
                  >> surj (incl (refree-pats tsx)) ◆ σ ∼ surj (incl (refree-pats tsy)) ◆ σ <<

                  ⟪ cong-∼ ⟫

                  >> map (surj (incl (refree-pats tsx)) ◆ σ) ∼ map (surj (incl (refree-pats tsy)) ◆ σ) <<

                  ⟪ functoriality-◆ {f = surj (incl (refree-pats tsx))} {g = σ} ≀∼≀ functoriality-◆ {f = surj (incl (refree-pats tsy))} {g = σ} ⟫

                  >> map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsx))) ◆ map σ ∼ map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsy))) ◆ map σ <<

                  ⟪ ((inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsx)})) ◈ refl ≀∼≀
                    ((inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsy)})) ◈ refl ⟫

                  >> (incl (refree-pats tsx)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ ∼ (incl (refree-pats tsy)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ <<

                  ⟪ ⟨_⟩ ⟫

                  >> (∀ i -> (refree-pats tsx i) ◆ reext ⟨ map σ ⟩ i ≡ (refree-pats tsy i) ◆ reext ⟨ map σ ⟩ i) <<

                  ⟪ destruct-precomp-free {f₀ = tsx} {f₁ = tsy} {g₀ = reext ⟨ map σ ⟩} {g₁ = reext ⟨ map σ ⟩} ⟫

                  >> (∀ i -> tsx i ◆ reext ⟨ map σ ⟩ (γₗ Γ i) ≡ tsy i ◆ reext ⟨ map σ ⟩ (γₗ Γ i)) <<

                  ⟪ funExt ⟫
                  ⟪ cong lam ⟫

                  >> (lam (λ i -> tsx i ◆ reext ⟨ map σ ⟩ (γₗ Γ i)) ≡ lam (λ i -> tsy i ◆ reext ⟨ map σ ⟩ (γₗ Γ i))) <<

                  ⟪ cong (app-var vx) ⟫
                  ⟪ cong incl ⟫
                  ⟪ ≡→≡-Str ⟫


      lem-3 : ∀{x} (σ : 𝔍 ⟶ x) -> (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var vx (lam tsx))) ≣ incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var vx (lam tsy))))
                                    ↔ (∀ (p : 1 ∍ tt) -> surj (incl (refree-pats tsx)) ◆ σ ≣ surj (incl (refree-pats tsy)) ◆ σ)
      lem-3 σ = lem-1 σ , lem-2 σ





      P = record
          { famC      = mfam
          ; coversC   = lem-3
          ; fampropsC = {!!}
          }
-}

  ----------------------------------------------------------
  -- the con/con case


  success-con-con : ∀{Γ Δ : List (Jdg₂ ⟨ K ⟩)} {α : ⟨ K ⟩} {j : 𝐏𝐚𝐭 K}

            -> (x : TermCon (Δ ⇒ α)) -> (ts : Pat-pats ⟨ j ⟩ Γ (ι Δ))
                                        -> (ts' : Pat-pats ⟨ j ⟩ Γ (ι Δ))
            -> isSplittableC (𝐏𝐚𝐭 K) 1 (incl (app-con x ts) , incl (app-con x ts')) (SplitP)
  success-con-con {Γ} {Δ} {α} {𝔍} (vx) (lam tsx) (lam tsy) = {!!} {- P
    where

      -- TODO: in the following, `surj` does not work, have to use `surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭` instead. (even though in another file it worked)
      mfam : 1 ∍ tt -> _
      mfam _ = incl (γₗ! Γ (ι Δ)) , surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsx)) , surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsy))


      lem-1 : ∀{x} (σ : 𝔍 ⟶ x) -> (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con vx (lam tsx))) ≣ incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con vx (lam tsy))))
                                    -> (∀ (p : 1 ∍ tt) -> surj (incl (refree-pats tsx)) ◆ σ ≣ surj (incl (refree-pats tsy)) ◆ σ)
      lem-1 σ p _ = p
                      ⟪ cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 ⟫
                      ⟪ cancel-injective-app-con' ⟫
                      ⟪ cancel-injective-lam ⟫

                      >> (∀ i -> tsx i ◆ reext ⟨ map σ ⟩ (γₗ Γ i) ≡ tsy i ◆ reext ⟨ map σ ⟩ (γₗ Γ i)) <<

                      ⟪ construct-precomp-free {f₀ = tsx} {f₁ = tsy} {g₀ = reext ⟨ map σ ⟩} {g₁ = reext ⟨ map σ ⟩} ⟫

                      >> (∀ i -> ((refree-pats tsx i)) ◆ reext ⟨ map σ ⟩ i ≡ ((refree-pats tsy i)) ◆ reext ⟨ map σ ⟩ i) <<

                      ⟪ incl ⟫

                      >> (incl (refree-pats tsx)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ ∼ (incl (refree-pats tsy)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ <<

                      ⟪ (sym (inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsx)})) ◈ refl ≀∼≀
                        (sym (inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsy)})) ◈ refl ⟫

                      >> map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsx))) ◆-𝐑𝐞𝐊𝐥𝐬 map σ ∼ map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsy))) ◆-𝐑𝐞𝐊𝐥𝐬 map σ <<

                      ⟪ functoriality-◆ {f = surj (incl (refree-pats tsx))} {g = σ} ⁻¹ ≀∼≀ functoriality-◆ {f = surj (incl (refree-pats tsy))} {g = σ} ⁻¹ ⟫

                      >> map (surj (incl (refree-pats tsx)) ◆ σ) ∼ map (surj (incl (refree-pats tsy)) ◆ σ) <<
                      ⟪ cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 ⟫
                      >> surj (incl (refree-pats tsx)) ◆ σ ∼ surj (incl (refree-pats tsy)) ◆ σ <<

      lem-2 : ∀{x} (σ : 𝔍 ⟶ x) -> (∀ (p : 1 ∍ tt) -> surj (incl (refree-pats tsx)) ◆ σ ≣ surj (incl (refree-pats tsy)) ◆ σ)
                                  -> (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con vx (lam tsx))) ≣ incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con vx (lam tsy))))
      lem-2 σ p = p (left-∍ incl)
                  >> surj (incl (refree-pats tsx)) ◆ σ ∼ surj (incl (refree-pats tsy)) ◆ σ <<

                  ⟪ cong-∼ ⟫

                  >> map (surj (incl (refree-pats tsx)) ◆ σ) ∼ map (surj (incl (refree-pats tsy)) ◆ σ) <<

                  ⟪ functoriality-◆ {f = surj (incl (refree-pats tsx))} {g = σ} ≀∼≀ functoriality-◆ {f = surj (incl (refree-pats tsy))} {g = σ} ⟫

                  >> map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsx))) ◆ map σ ∼ map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (refree-pats tsy))) ◆ map σ <<

                  ⟪ ((inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsx)})) ◈ refl ≀∼≀
                    ((inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {f = incl (refree-pats tsy)})) ◈ refl ⟫

                  >> (incl (refree-pats tsx)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ ∼ (incl (refree-pats tsy)) ◆-𝐑𝐞𝐊𝐥𝐬 map σ <<

                  ⟪ ⟨_⟩ ⟫

                  >> (∀ i -> (refree-pats tsx i) ◆ reext ⟨ map σ ⟩ i ≡ (refree-pats tsy i) ◆ reext ⟨ map σ ⟩ i) <<

                  ⟪ destruct-precomp-free {f₀ = tsx} {f₁ = tsy} {g₀ = reext ⟨ map σ ⟩} {g₁ = reext ⟨ map σ ⟩} ⟫

                  >> (∀ i -> tsx i ◆ reext ⟨ map σ ⟩ (γₗ Γ i) ≡ tsy i ◆ reext ⟨ map σ ⟩ (γₗ Γ i)) <<

                  ⟪ funExt ⟫
                  ⟪ cong lam ⟫

                  >> (lam (λ i -> tsx i ◆ reext ⟨ map σ ⟩ (γₗ Γ i)) ≡ lam (λ i -> tsy i ◆ reext ⟨ map σ ⟩ (γₗ Γ i))) <<

                  ⟪ cong (app-con vx) ⟫
                  ⟪ cong incl ⟫
                  ⟪ ≡→≡-Str ⟫


      lem-3 : ∀{x} (σ : 𝔍 ⟶ x) -> (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con vx (lam tsx))) ≣ incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con vx (lam tsy))))
                                    ↔ (∀ (p : 1 ∍ tt) -> surj (incl (refree-pats tsx)) ◆ σ ≣ surj (incl (refree-pats tsy)) ◆ σ)
      lem-3 σ = lem-1 σ , lem-2 σ





      P = record
          { famC      = mfam
          ; coversC   = lem-3
          ; fampropsC = {!!}
          }

-}
