
{-# OPTIONS --experimental-lossy-unification #-}
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Var where

open import Verification.Conventions hiding (Structure)

-- open import Verification.Core.Conventions hiding (Structure ; isSetoid:byPath)
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
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Property.Base
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Reflection
open import Verification.Core.Category.Std.Category.Sized.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Size



module _ {𝑨 : 𝕋× 𝑖} where
  module _ {s : Type 𝑨} {Γ : 𝐂𝐭𝐱 𝑨} (x y : ⟨ Γ ⟩ ∍ s) (y≠x : y ≠-∍ x) where

    lem-11 : hasSizedCoequalizer {𝒞 = 𝐂𝐭𝐱 𝑨} (simpleVar x) (simpleVar y)
    lem-11 = Γ' since (isCoequalizer:byFullyFaithfull lem-10) , right lem-12
      where
        T : RelativeMonad (𝑓𝑖𝑛 (Type 𝑨))
        T = ′ Term-𝕋× 𝑨 ′

        Γ' : 𝐂𝐭𝐱 𝑨
        Γ' = incl (⟨ Γ ⟩ \\ x)

        π' : ι Γ ⟶ ι Γ'
        π' = incl (⟨ (π-\\ x y y≠x) ⟩ ◆ repure)

        ι' : ι Γ' ⟶ ι Γ
        ι' = incl (ι-\\ x ◆ repure)


        lem-01 : ∀ i z -> ⟨ (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (⧜subst (incl (var x)))) ◆ π' ⟩ i z ≡ ⟨ (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (⧜subst (incl (var y)))) ◆ π' ⟩ i z
        lem-01 i incl = ≡-Str→≡ (cong-Str var (π-\\-∼ y≠x))

        equate-π₌' : map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (⧜subst (incl (var x))) ◆ π' ∼ map ((⧜subst (incl (var y)))) ◆ π'
        equate-π₌' = incl (λ i -> funExt (lem-01 i))

        lem-08 : ∀{c : 𝐒𝐮𝐛𝐬𝐭 T} -> (h : ι (Γ) ⟶ c) -> (p : map (⧜subst (incl (var x))) ◆ h ∼ map (⧜subst (incl (var y))) ◆ h)
                -> ∑ λ (ξ : ι (Γ') ⟶ c) -> π' ◆ ξ ∼ h
        lem-08 {c} h p = ξ , P
          where
            ξ : ι (Γ') ⟶ c
            ξ = ι' ◆ h

            P-8 : ⟨ h ⟩ s x ≡ ⟨ h ⟩ s y
            P-8 = funExt⁻¹ (⟨ p ⟩ s) incl

            P-9 : (i : Sort 𝑨) (z : ⟨ Γ ⟩ ∍ i) →
                  ⟨ h ⟩ i (ι-\\ x i (⟨ π-\\ x y y≠x ⟩ i z))  ≡  ⟨ h ⟩ i z
            P-9 i z with merge-embed y≠x z
            ... | left x = cong (⟨ h ⟩ i) (≡-Str→≡ x)
            ... | just refl-≣-2 =
              ⟨ h ⟩ i (ι-\\ z i (⟨ π-\\ z y y≠x ⟩ i z))  ⟨ cong (⟨ h ⟩ i) (≡-Str→≡ (merge-single y≠x)) ⟩-≡
              ⟨ h ⟩ i y                                  ⟨ sym-Path P-8 ⟩-≡
              ⟨ h ⟩ i z                                  ∎-≡

            P : π' ◆ (ι' ◆ h) ∼ h
            P = incl (λ i -> funExt (P-9 i))

        cancel-epi-π' : ∀{z : 𝐒𝐮𝐛𝐬𝐭 T} -> {f g : ι Γ' ⟶ z} -> (π' ◆ f ∼ π' ◆ g) -> f ∼ g
        cancel-epi-π' {z} {f} {g} p = incl λ i -> funExt (P-9 i)
          where
            P-8 : ∀ (i : Sort 𝑨) (z : ⟨ Γ' ⟩ ∍ i) ->  ⟨ f ⟩ i (⟨ π-\\ x y y≠x ⟩ i (ι-\\ x i z)) ≡ ⟨ g ⟩ i (⟨ π-\\ x y y≠x ⟩ i (ι-\\ x i z))
            P-8 i z = funExt⁻¹ (⟨ p ⟩ i) (ι-\\ x i z)

            P-9 : ∀ (i : Sort 𝑨) (z : ⟨ Γ' ⟩ ∍ i) -> ⟨ f ⟩ i z ≡ ⟨ g ⟩ i z
            P-9 i z = _ ⟨ sym-Path (cong (⟨ f ⟩ i) (≡-Str→≡ (embed-merge y≠x z))) ⟩-≡
                      _ ⟨ P-8 i z ⟩-≡
                      _ ⟨ (cong (⟨ g ⟩ i) (≡-Str→≡ (embed-merge y≠x z))) ⟩-≡
                      _ ∎-≡

        lem-09 : isEpi (π')
        lem-09 = epi cancel-epi-π'


        lem-10 : isCoequalizer (map (⧜subst (incl (var x)))) (map (⧜subst (incl (var y)))) (ι Γ')
        isCoequalizer.π₌ lem-10 = π'
        isCoequalizer.equate-π₌ lem-10 = equate-π₌'
        isCoequalizer.compute-Coeq lem-10 = lem-08
        isCoequalizer.isEpi:π₌ lem-10 = lem-09

        lem-12 : 人length ⟨ ⟨ ι Γ' ⟩ ⟩ ≪-𝒲-𝕋× 人length ⟨ Γ ⟩
        lem-12 =  incl (zero , (§-\\.prop-1 {as = ⟨ Γ ⟩} ⁻¹ ))




    hasCoequalizer:varvar : hasCoequalizer {𝒞 = 𝐂𝐭𝐱 𝑨} (simpleVar x) (simpleVar y)
    hasCoequalizer:varvar = hasCoequalizer:this lem-11


    hasSizedCoequalizer:varvar : hasSizedCoequalizer {𝒞 = 𝐂𝐭𝐱 𝑨} (simpleVar x) (simpleVar y)
    hasSizedCoequalizer:varvar = lem-11
  -- record hasSizedCoequalizer {a b : 𝒞} (f g : a ⟶ b) : 𝒰 𝑖 where





