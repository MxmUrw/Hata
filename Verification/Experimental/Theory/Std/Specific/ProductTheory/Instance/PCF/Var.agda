
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Var where

open import Verification.Conventions hiding (Structure)

-- open import Verification.Experimental.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything -- hiding (isSetoid:Function)
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

open import Verification.Experimental.Data.List.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.FiniteIndexed.Property.Merge

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem



module _ {𝑨 : 𝕋× 𝑖} where
  module _ {s : Type 𝑨} {Γ : 𝐂𝐭𝐱 𝑨} (x y : ⟨ Γ ⟩ ∍ s) (y≠x : y ≠-∍ x) where

    lem-11 : hasCoequalizer {X = 𝐂𝐭𝐱 𝑨} (simpleVar x) (simpleVar y)
    lem-11 = Γ' since (isCoequalizer:byFullyFaithfull lem-10)
      where
        T : RelativeMonad (𝑓𝑖𝑛 (Type 𝑨))
        T = ′ Term-𝕋× 𝑨 ′

        Γ' : 𝐂𝐭𝐱 𝑨
        Γ' = incl (⟨ Γ ⟩ \\ x)

        π' : ι Γ ⟶ ι Γ'
        π' = incl (⟨ (π-\\ x y y≠x) ⟩ ◆ repure)

        ι' : ι Γ' ⟶ ι Γ
        ι' = incl (ι-\\ x ◆ repure)


        lem-01 : ∀ i z -> ⟨ (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (var x))) ◆ π' ⟩ i z ≡ ⟨ (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (var y))) ◆ π' ⟩ i z
        lem-01 i incl = ≡-Str→≡ (cong-Str var (π-\\-∼ y≠x))

        equate-π₌' : map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (var x)) ◆ π' ∼ map (incl (var y)) ◆ π'
        equate-π₌' = incl (λ i -> funExt (lem-01 i))

        lem-08 : ∀{c : 𝐒𝐮𝐛𝐬𝐭 T} -> (h : ι (Γ) ⟶ c) -> (p : map (incl (var x)) ◆ h ∼ map (incl (var y)) ◆ h)
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


        lem-10 : isCoequalizer (map (incl (var x))) (map (incl (var y))) (ι Γ')
        isCoequalizer.π₌ lem-10 = π'
        isCoequalizer.equate-π₌ lem-10 = equate-π₌'
        isCoequalizer.compute-Coeq lem-10 = lem-08
        isCoequalizer.isEpi:π₌ lem-10 = lem-09



    hasCoequalizer:varvar : hasCoequalizer {X = 𝐂𝐭𝐱 𝑨} (simpleVar x) (simpleVar y)
    hasCoequalizer:varvar = lem-11





