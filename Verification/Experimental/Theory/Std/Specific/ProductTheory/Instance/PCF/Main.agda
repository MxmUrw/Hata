
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Main where

open import Verification.Conventions

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
-- open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
-- open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder 
open import Verification.Experimental.Order.Lattice hiding (⊥)

open import Verification.Experimental.Data.List.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.FiniteIndexed.Property.Merge
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Base
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.DirectFail

module _ {𝑨 : 𝕋× 𝑖} where

  ∂-𝕋× : ∀{x y : 𝐂𝐭𝐱 𝑨} -> (t : Pair x y) -> (isBase-𝕋× t +-𝒰 (∑ λ n -> isSplittableC (𝐂𝐭𝐱 𝑨) n t SplitP))
  ∂-𝕋× (◌-⧜ , ◌-⧜) = left isBase:⊥
  -- ∂-𝕋× {x} {y} ((f₀ ⋆-⧜ f₁) , (g₀ ⋆-⧜ g₁)) = right (2 , record { famC = fam' ; coversC = (λ h -> covers-0 h , covers-1 h) ; fampropsC = {!!} })
  --   where
  --     fam' : 2 ∍ tt -> ∑ λ x' -> Pair x' y
  --     fam' (right-∍ i) = _ , f₀ , g₀
  --     fam' (left-∍ i) = _ , f₁ , g₁

  --     covers-0 : {x = x₁ : 𝐂𝐭𝐱ᵘ 𝑨} (h : y ⟶ x₁) →
  --               ((f₀ ◆ h) ⋆-⧜ (f₁ ◆ h) ∼ (g₀ ◆ h) ⋆-⧜ (g₁ ◆ h))
  --               ->
  --               ((p : 2 ∍ tt) →
  --               (fst (fam' p .snd) ◆ h)
  --               ∼ (snd (fam' p .snd) ◆ h))
  --     covers-0 {x = x₁} h q (right-∍ p) = π₀-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ q
  --     covers-0 {x = x₁} h q (left-∍ p) = π₁-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ q

  --     covers-1 : {x = x₁ : 𝐂𝐭𝐱ᵘ 𝑨} (h : y ⟶ x₁) →
  --               ((p : 2 ∍ tt) →
  --               (fst (fam' p .snd) ◆ h)
  --               ∼ (snd (fam' p .snd) ◆ h))
  --               -> ((f₀ ◆ h) ⋆-⧜ (f₁ ◆ h) ∼ (g₀ ◆ h) ⋆-⧜ (g₁ ◆ h))
  --     covers-1 h p = cong₂-Str _⋆-⧜_ (p (right-∍ (left-∍ incl))) (p (left-∍ incl))


  -- ∂-𝕋× (incl (var x) , incl (var y)) with compare-∍ y x
  -- ... | left ¬p = left (isBase:var _ _ ¬p)
  -- ... | right (p , q) with isset-Str p refl-≣
  -- ∂-𝕋× (incl (var x) , incl (var .x)) | just (.refl-≣ , refl-≣) | refl-≣ = left isBase:id
  -- ∂-𝕋× (incl (var x) , incl (con c x₁)) = left (isBase:sym (isBase:con-var _ _ _))
  -- ∂-𝕋× (incl (con c x) , incl (var x₁)) = left (isBase:con-var _ _ _)
  ∂-𝕋× (incl (con {αs = αsx} cx tsx) , incl (con {αs = αsy} cy tsy)) with αsx ≟-Str αsy
  ... | no ¬p = left (isBase:con≠con cx cy tsx tsy ¬p)
  ... | yes refl-≣ with cx ≟-Str cy
  ... | no ¬p = left (isBase:con≠con₂ cx cy tsx tsy ¬p)
  ... | yes refl-≣ with tsx | tsy
  ... | incl-Terms f | incl-Terms g = right (1 , record { famC = fam' ; coversC = λ h → covers-0 h , {!!} ; fampropsC = {!!} })
    where
      f₀ = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl f)
      g₀ = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl g)

      fam' : 1 ∍ tt -> _
      fam' x = _ , f₀ , g₀

      covers-0 : {x : 𝐂𝐭𝐱ᵘ 𝑨}
                    (h : incl _ ⟶ x) →
                    incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h (con cx (incl-Terms f))) ∼ (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h (con cx (incl-Terms g))))
                    ->
                    ((p : 1 ∍ tt) →
                    ((fst (fam' p .snd) ◆-⧜𝐒𝐮𝐛𝐬𝐭 h))
                    ∼ (snd (fam' p .snd) ◆-⧜𝐒𝐮𝐛𝐬𝐭 h))
      covers-0 h p q = p
        >> incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h (con cx (incl-Terms f))) ∼ (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h (con cx (incl-Terms g)))) <<
        ⟪ cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 ⟫
        ⟪ cancel-injective-con₃ refl-≣ ⟫
        ⟪ cancel-injective-incl-Terms ⟫
        ⟪ incl ⟫

        >> ((incl f) ◆ map h) ∼ ((incl g) ◆ map h) <<

        ⟪ inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 ⁻¹ ◈ refl ≀∼≀ inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 ⁻¹ ◈ refl ⟫

        >> (map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl f)) ◆ map h) ∼ (map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl g)) ◆ map h) <<

        ⟪  functoriality-◆ {f = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl f)} {g = h} ⁻¹ ≀∼≀
           functoriality-◆ {f = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl g)} {g = h} ⁻¹ ⟫

        >> (map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl f) ◆ h)) ∼ (map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl g) ◆ h)) <<

        ⟪ cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 ⟫

        >> (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl f) ◆-⧜𝐒𝐮𝐛𝐬𝐭 h) ∼ (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl g) ◆-⧜𝐒𝐮𝐛𝐬𝐭 h) <<


  ∂-𝕋× = {!!}


