
{-# OPTIONS --no-qualified-instances #-}

module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Base where

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
-- open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Property.Base
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

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2


WF-𝕋× : 𝒰₀
WF-𝕋× = ℕ ^ 3

macro 𝒲-𝕋× = #structureOn WF-𝕋×

postulate
  _≪-𝒲-𝕋×_ : 𝒲-𝕋× -> 𝒲-𝕋× -> 𝒰 ℓ₀
  WellFounded-≪-𝒲-𝕋× : WellFounded _≪-𝒲-𝕋×_


instance
  isWellfounded:𝒲-𝕋× : isWF {ℓ₀} ℓ₀ 𝒲-𝕋×
  isWellfounded:𝒲-𝕋× = record { _≪_ = _≪-𝒲-𝕋×_ ; wellFounded = WellFounded-≪-𝒲-𝕋× }

instance
  isWFT:𝒲-𝕋× : isWFT 𝒲-𝕋×
  isWFT:𝒲-𝕋× = {!!}



module _ {𝑨 : 𝕋× 𝑖} where
  instance
    isDiscrete:𝐂𝐭𝐱-𝕋× : isDiscrete (𝐂𝐭𝐱 𝑨)
    isDiscrete:𝐂𝐭𝐱-𝕋× = {!!}

    isSet-Str:𝐂𝐭𝐱-𝕋× : isSet-Str (𝐂𝐭𝐱 𝑨)
    isSet-Str:𝐂𝐭𝐱-𝕋× = {!!}

    isSet-Str:Type-𝕋× : isSet-Str (Type 𝑨)
    isSet-Str:Type-𝕋× = {!!}


  data isBase-𝕋× : ∀{x y : 𝐂𝐭𝐱 𝑨} -> Pair x y -> 𝒰 𝑖 where
    isBase:⊥ : ∀{x : 𝐂𝐭𝐱 𝑨} -> {f g : ⊥ ⟶ x} -> isBase-𝕋× (f , g)
    isBase:sym : ∀{x y : 𝐂𝐭𝐱 𝑨} -> {f g : x ⟶ y} -> isBase-𝕋× (f , g) -> isBase-𝕋× (g , f)
    isBase:id : ∀{x y : 𝐂𝐭𝐱 𝑨} -> {f : x ⟶ y} -> isBase-𝕋× (f , f)
    isBase:var : ∀{s : Type 𝑨} {Γ : 𝐂𝐭𝐱 𝑨} (x y : ⟨ Γ ⟩ ∍ s) -> (y ≠-∍ x) -> isBase-𝕋× (incl (var x) , incl (var y))
    -- isBase:var-con : ∀{s : Type 𝑨} {Γ : 𝐂𝐭𝐱 𝑨} -> (x : ⟨ Γ ⟩ ∍ s) -> (t : Γ ⊢ s) -> isBase-𝕋× (incl (var x) , t)

  postulate
    size-𝕋× : ∀{a b : 𝐂𝐭𝐱 𝑨} -> Pair a b -> 𝒲-𝕋×

  SplitP : IxC (𝐂𝐭𝐱 𝑨) -> IxC (𝐂𝐭𝐱 𝑨) -> 𝒰₀
  SplitP (_ , _ , i) = (λ (_ , _ , j) -> size-𝕋× j ≪-𝒲-𝕋× size-𝕋× i)


  decide-Base-𝕋× : ∀{a b : 𝐂𝐭𝐱 𝑨} -> ∀(f g : a ⟶ b) -> isBase-𝕋× (f , g) -> isDecidable (hasCoequalizer f g)
  decide-Base-𝕋× f g isBase:⊥ = right hasCoequalizer:byInitial
  decide-Base-𝕋× f g (isBase:sym p) = {!!}
  decide-Base-𝕋× f .f isBase:id = {!!}
  decide-Base-𝕋× .(incl (var x)) .(incl (var y)) (isBase:var {s} {Γ} x y y≠x) = right lem-12
    where
      T : RelativeMonad (𝑓𝑖𝑛 (Type 𝑨))
      T = ′ Term-𝕋× 𝑨 ′

      Γ' : 𝐂𝐭𝐱 𝑨
      Γ' = incl (⟨ Γ ⟩ \\ x)

      π' : ι Γ ⟶ ι Γ'
      π' = incl (⟨ (π-\\ x y y≠x) ⟩ ◆ repure)

      lem-01 : ∀ i z -> ⟨ (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (var x))) ◆ π' ⟩ i z ≡ ⟨ (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (var y))) ◆ π' ⟩ i z
      lem-01 i incl = ≡-Str→≡ (cong-Str var (π-\\-∼ y≠x))

      equate-π₌' : map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (var x)) ◆ π' ∼ map (incl (var y)) ◆ π'
      equate-π₌' = incl (λ i -> funExt (lem-01 i))

      lem-08 : ∀{c : 𝐒𝐮𝐛𝐬𝐭 T} -> (h : ι (Γ) ⟶ c) -> (p : map (incl (var x)) ◆ h ∼ map (incl (var y)) ◆ h)
               -> ∑ λ (ξ : ι (Γ') ⟶ c) -> π' ◆ ξ ∼ h
      lem-08 {c} h p = ξ , P
        where
          ι' : ι Γ' ⟶ ι Γ
          ι' = incl (ι-\\ x ◆ repure)

          ξ : ι (Γ') ⟶ c
          ξ = ι' ◆ h

          P-8 : ⟨ h ⟩ s x ≡ ⟨ h ⟩ s y
          P-8 = funExt⁻¹ (⟨ p ⟩ s) incl

          P-9 : (i : Sort 𝑨) (z : ⟨ Γ ⟩ ∍ i) →
                ⟨ h ⟩ i (ι-\\ x i (⟨ π-\\ x y y≠x ⟩ i z))  ≡  ⟨ h ⟩ i z
          P-9 i z with merge-embed y≠x z
          ... | left x = cong (⟨ h ⟩ i) (≡-Str→≡ x)
          ... | just refl-=-∍ =
            ⟨ h ⟩ i (ι-\\ z i (⟨ π-\\ z y y≠x ⟩ i z))  ⟨ cong (⟨ h ⟩ i) (≡-Str→≡ (merge-single y≠x)) ⟩-≡
            ⟨ h ⟩ i y                                  ⟨ sym-Path P-8 ⟩-≡
            ⟨ h ⟩ i z                                  ∎-≡

          P : π' ◆ (ι' ◆ h) ∼ h
          P = incl (λ i -> funExt (P-9 i))


      lem-10 : isCoequalizer (map (incl (var x))) (map (incl (var y))) (ι Γ')
      isCoequalizer.π₌ lem-10 = π'
      isCoequalizer.equate-π₌ lem-10 = equate-π₌'
      isCoequalizer.compute-Coeq lem-10 = lem-08
      isCoequalizer.isEpi:π₌ lem-10 = {!!}

      lem-11 : hasCoequalizer (map (incl (var x))) (map (incl (var y)))
      lem-11 = (ι Γ') since lem-10

      lem-12 : hasCoequalizer _ _
      lem-12 = Γ' since {!!}






