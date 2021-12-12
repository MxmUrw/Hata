
module Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.PCF.Size where

open import Verification.Conventions hiding (Structure ; ℕ)

-- open import Verification.Core.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Contradiction
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
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
open import Verification.Core.Category.Std.Category.Sized.Definition
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Property.Base
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Reflection
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.WellFounded.Construction.Product
open import Verification.Core.Order.WellFounded.Construction.Sum
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.FormalSystem

open import Verification.Core.Computation.Unification.Categorical.PrincipalFamilyCat



WF-𝕋× : 𝒰₀
WF-𝕋× = ℕ

macro 𝒲-𝕋× = #structureOn WF-𝕋×

_≪-𝒲-𝕋×_ : 𝒲-𝕋× -> 𝒲-𝕋× -> 𝒰 ℓ₀
_≪-𝒲-𝕋×_ m n = (1 ⋆ m) ≤ n





----------------------------------------------------------
-- NOTE: Wellfoundedness proof copied from cubical std library

private
  _<_ = _≪-𝒲-𝕋×_

  <-split : m < suc n → (m < n) +-𝒰 (m ≣ n)
  <-split {n = zero} (incl (zero , refl-≣)) = right refl-≣
  <-split {n = zero} (incl (suc zero , ()))
  <-split {n = zero} (incl (suc (suc a) , ()))
  <-split {zero} {suc n} p = left (incl (n , comm-⋆ {a = n}))
  <-split {suc m} {suc n} p with <-split (incl (pred-≤-pred ⟨ p ⟩))
  ... | left x = left (incl (suc-≤-suc ⟨ x ⟩))
  ... | just x = right (cong-Str suc x)

  acc-suc : Acc _<_ n → Acc _<_ (suc n)
  acc-suc a = acc λ y y<sn
              → case (<-split y<sn) of
                     (λ y<n → access a y y<n)
                     (λ y≣n → subst-Str _ (sym y≣n) a)


WellFounded-≪-𝒲-𝕋× : WellFounded _≪-𝒲-𝕋×_
WellFounded-≪-𝒲-𝕋× zero = acc (λ y (incl p) → impossible (¬-<-zero p))
WellFounded-≪-𝒲-𝕋× (suc x) = acc-suc (WellFounded-≪-𝒲-𝕋× x)

-- WF proof end
----------------------------------------------------------


----------------------------------------------------------

instance
  isWellfounded:𝒲-𝕋× : isWF {ℓ₀} ℓ₀ 𝒲-𝕋×
  isWellfounded:𝒲-𝕋× = record { _≪_ = _≪-𝒲-𝕋×_ ; wellFounded = WellFounded-≪-𝒲-𝕋× }

private
  lem-1 : ∀{a : ℕ} -> 0 ⪣ a
  lem-1 {a = zero} = left refl-≣
  lem-1 {a = suc a} = right (incl (a , comm-⋆ {a = a} {b = 1}))

instance
  isWFT:𝒲-𝕋× : isWFT 𝒲-𝕋×
  isWFT:𝒲-𝕋× = record { _⟡-≪_ = λ x y → incl (<-trans ⟨ x ⟩ ⟨ y ⟩) }

instance
  isWFT0:ℕ : isWFT0 ℕ
  isWFT0:ℕ = record { ⊥-WFT = 0 ; initial-⊥-WFT = lem-1 }

module _ {𝑨 : 𝕋× 𝑖} where
  mutual
    sizeC-Term : ∀{a} {b} -> (Term₁-𝕋× 𝑨 a b) -> ℕ
    sizeC-Term (var x) = zero
    sizeC-Term (con c x) = suc (sizeC-half (⧜subst x))

    sizeC-half : ∀{a b : 𝐂𝐭𝐱 𝑨} -> (f : a ⟶ b) -> ℕ
    sizeC-half (⧜subst ◌-⧜) = zero
    sizeC-half (⧜subst (incl x)) = sizeC-Term x
    sizeC-half (⧜subst (a ⋆-⧜ b)) = suc (sizeC-half (⧜subst a) ⋆ sizeC-half (⧜subst b))

  sizeC-𝕋× : ∀{a b : 𝐂𝐭𝐱 𝑨} -> (f : HomPair a b) -> Maybe (ℕᵘ × ℕᵘ)
  sizeC-𝕋× (f , g) = just (sizeC-half f , sizeC-half g)

  instance
    isSizedCategory:𝐂𝐭𝐱-𝕋× : isSizedCategory (𝐂𝐭𝐱 𝑨)
    isSizedCategory:𝐂𝐭𝐱-𝕋× = record
      { SizeO = ℕ
      ; sizeO = λ x → 人length ⟨ x ⟩
      }

  instance
    isSizedHomPairCategory:𝐂𝐭𝐱-𝕋× : isSizedHomPairCategory (𝐂𝐭𝐱 𝑨)
    isSizedHomPairCategory:𝐂𝐭𝐱-𝕋× = record
      { SizeC = ′ Maybe (ℕᵘ ×-𝒰 ℕᵘ) ′
      ; sizeC = sizeC-𝕋×
      ; cong-sizeC = λ {f g (refl-≣ , refl-≣) → refl-≣}
      }

    -- record { SizeC = ′ ℕᵘ ×-𝒰 ℕᵘ ′ ; sizeC = sizeC-𝕋×  }

ι₀-≪-⋆-ℕ : ∀{a b : ℕ} -> a ≤ (a ⋆ b)
ι₀-≪-⋆-ℕ {a} {b} = incl (b , comm-⋆ {a = b} {b = a})


