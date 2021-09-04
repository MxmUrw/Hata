
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Size where

open import Verification.Conventions hiding (Structure ; ℕ)

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
open import Verification.Experimental.Data.Nat.Definition
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

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} (R : A -> A -> 𝒰 𝑘) (S : B -> B -> 𝒰 𝑙) where
  ×-≪ : (A × B) -> (A × B) -> 𝒰 (𝑘 ､ 𝑙)
  ×-≪ (a , b) (a2 , b2) = R a a2 × S b b2

  private T = ×-≪

  module _ (p : WellFounded R) (q : WellFounded S) where
    private
      lem-3 : ∀ a b -> Acc R a -> Acc S b -> Acc T (a , b)
      lem-3 a b (acc racc) (acc sacc) = acc λ (a1 , b1) (r1 , s1) → lem-3 a1 b1 (racc a1 r1) (sacc b1 s1)

      lem-1 : ∀ x -> Acc T x
      lem-1 (a0 , b0) = lem-3 a0 b0 (p a0) (q b0)

    WellFounded:× : WellFounded T
    WellFounded:× = lem-1

module _ {A : 𝒰 𝑖} {{_ : isWF 𝑗 A}}
         {B : 𝒰 𝑘} {{_ : isWF 𝑙 B}} where
  instance
    isWF:× : isWF _ (A × B)
    isWF:× = record { _≪_ = ×-≪ _≪_ _≪_ ; wellFounded = WellFounded:× _≪_ _≪_ wellFounded wellFounded }

  module _ {{_ : isWFT ′ A ′}} {{_ : isWFT ′ B ′}} where
    instance
      isWFT:× : isWFT (A × B)
      isWFT:× = {!!}


WF-𝕋× : 𝒰₀
WF-𝕋× = ℕ

macro 𝒲-𝕋× = #structureOn WF-𝕋×

_≪-𝒲-𝕋×_ : 𝒲-𝕋× -> 𝒲-𝕋× -> 𝒰 ℓ₀
_≪-𝒲-𝕋×_ m n = (1 ⋆ m) ≤ n

postulate
  WellFounded-≪-𝒲-𝕋× : WellFounded _≪-𝒲-𝕋×_

instance
  isWellfounded:𝒲-𝕋× : isWF {ℓ₀} ℓ₀ 𝒲-𝕋×
  isWellfounded:𝒲-𝕋× = record { _≪_ = _≪-𝒲-𝕋×_ ; wellFounded = WellFounded-≪-𝒲-𝕋× }

instance
  isWFT:𝒲-𝕋× : isWFT 𝒲-𝕋×
  isWFT:𝒲-𝕋× = record { _⟡-≪_ = λ x y → incl (<-trans ⟨ x ⟩ ⟨ y ⟩) }

module _ {𝑨 : 𝕋× 𝑖} where
  mutual
    sizeC-Term : ∀{a} {b} -> (Term₁-𝕋× 𝑨 a b) -> ℕ
    sizeC-Term (var x) = zero
    sizeC-Term (con c x) = suc (sizeC-half (⧜subst x))

    sizeC-half : ∀{a b : 𝐂𝐭𝐱 𝑨} -> (f : a ⟶ b) -> ℕ
    sizeC-half (⧜subst ◌-⧜) = zero
    sizeC-half (⧜subst (incl x)) = sizeC-Term x
    sizeC-half (⧜subst (a ⋆-⧜ b)) = suc (sizeC-half (⧜subst a) ⋆ sizeC-half (⧜subst b))

  sizeC-𝕋× : ∀{a b : 𝐂𝐭𝐱 𝑨} -> (f : Pair a b) -> ℕᵘ × ℕᵘ
  sizeC-𝕋× (f , g) = sizeC-half f , sizeC-half g

  instance
    isSizedCategory:𝐂𝐭𝐱-𝕋× : isSizedCategory (𝐂𝐭𝐱 𝑨)
    isSizedCategory:𝐂𝐭𝐱-𝕋× = record { SizeC = ′ ℕᵘ ×-𝒰 ℕᵘ ′ ; sizeC = sizeC-𝕋× ; size0 = (0 , 0) ; initial-size0 = {!!} }

ι₀-≪-⋆-ℕ : ∀{a b : ℕ} -> a ≤ (a ⋆ b)
ι₀-≪-⋆-ℕ {a} {b} = incl ({!!} , {!!})


