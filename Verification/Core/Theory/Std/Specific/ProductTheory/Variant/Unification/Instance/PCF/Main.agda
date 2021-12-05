
module Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.PCF.Main where

open import Verification.Conventions hiding (ℕ)

open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
-- open import Verification.Core.Category.Std.Category.Subcategory.Definition
-- open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.WellFounded.Construction.Product
open import Verification.Core.Order.WellFounded.Construction.Sum
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.FormalSystem

open import Verification.Core.Computation.Unification.Categorical.PrincipalFamilyCat

open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.PCF.Base
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.PCF.Size
open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.PCF.DirectFail

module _ {𝑨 : 𝕋× 𝑖} where

  ∂-𝕋× : ∀{x y : 𝐂𝐭𝐱 𝑨} -> (t : HomPair x y) -> (isBase-𝕋× t +-𝒰 (∑ λ n -> isSplittableC (𝐂𝐭𝐱 𝑨) n t))
  ∂-𝕋× (⧜subst ◌-⧜ , ⧜subst ◌-⧜) = left isBase:⊥
  ∂-𝕋× {x} {y} (⧜subst (f₀ ⋆-⧜ f₁) , ⧜subst (g₀ ⋆-⧜ g₁)) = right (2 , record
    { famC = fam'
    ; coversC = ? -- (λ h -> covers-0 h , covers-1 h)
    ; fampropsC = sizes
    })
    where
      fam' : Fin-R 2 -> ∑ λ x' -> HomPair x' y
      fam' (zero) = _ , ⧜subst f₀ , ⧜subst g₀
      fam' (suc zero) = _ , ⧜subst f₁ , ⧜subst g₁

      covers-0 : {x = x₁ : 𝐂𝐭𝐱ᵘ 𝑨} (h : y ⟶ x₁) →
                (⧜subst ((f₀ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h) ⋆-⧜ (f₁ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h)))
                      ∼ (⧜subst ((g₀ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h) ⋆-⧜ (g₁ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h))) →
                      (p : Fin-R 2) →
                      (⧜subst (⟨ fst (fam' p .snd) ⟩ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h))
                      ∼ (⧜subst (⟨ snd (fam' p .snd) ⟩ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h))

      covers-0 {x = x₁} h q (zero) = π₀-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ q
      covers-0 {x = x₁} h q (suc zero) = π₁-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ q

      covers-1 : {x = x₁ : 𝐂𝐭𝐱ᵘ 𝑨} (h : y ⟶ x₁) →
                      ((p : Fin-R 2) →
                      (⧜subst (⟨ fst (fam' p .snd) ⟩ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h))
                      ∼ (⧜subst (⟨ snd (fam' p .snd) ⟩ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h))) ->
                      (⧜subst ((f₀ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h) ⋆-⧜ (f₁ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h)))
                            ∼ (⧜subst ((g₀ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h) ⋆-⧜ (g₁ ◆-⧜𝐒𝐮𝐛𝐬𝐭' h)))

      covers-1 h p = cong-Str ⧜subst (cong₂-Str _⋆-⧜_ (cong-Str ⟨_⟩ (p (zero))) (cong-Str ⟨_⟩ (p (suc zero))))

      sizes : ∀(k : Fin-R 2) -> sizeC (fam' k .snd) ≪ sizeC (⧜subst (f₀ ⋆-⧜ f₁) , ⧜subst (g₀ ⋆-⧜ g₁))
      sizes (zero) = right ((incl (sizeC-half (⧜subst f₁) , comm-⋆ {a = sizeC-half (⧜subst f₁)} {b = _})) , (incl (sizeC-half (⧜subst g₁) , comm-⋆ {a = sizeC-half (⧜subst g₁)} {b = _})))
      sizes (suc zero) = right (incl (sizeC-half (⧜subst f₀) , (+-suc (sizeC-half (⧜subst f₀)) _)) , incl (sizeC-half (⧜subst g₀) , (+-suc (sizeC-half (⧜subst g₀)) _)))


  ∂-𝕋× (⧜subst (incl (var x)) , ⧜subst (incl (var y))) with compare-∍ y x
  ... | left ¬p = left (isBase:var _ _ ¬p)
  ... | right (p , q) with isset-Str p refl-≣
  ∂-𝕋× (⧜subst (incl (var x)) , ⧜subst (incl (var .x))) | just (.refl-≣ , refl-≣) | refl-≣ = left isBase:id
  ∂-𝕋× (⧜subst (incl (var x)) , ⧜subst (incl (con c x₁))) = left (isBase:sym (isBase:con-var _ _ _))
  ∂-𝕋× (⧜subst (incl (con c x)) , ⧜subst (incl (var x₁))) = left (isBase:con-var _ _ _)
  ∂-𝕋× (⧜subst (incl (con {αs = αsx} cx tsx)) , ⧜subst (incl (con {αs = αsy} cy tsy))) with αsx ≟-Str αsy
  ... | no ¬p = left (isBase:con≠con cx cy tsx tsy ¬p)
  ... | yes refl-≣ with cx ≟-Str cy
  ... | no ¬p = left (isBase:con≠con₂ cx cy tsx tsy ¬p)
  ... | yes refl-≣ = right (1 , record { famC = fam' ; coversC = λ h → covers-0 h , covers-1 h ; fampropsC = λ k → right (reflexive , reflexive) })
    where
      f₀ = ⧜subst (tsx)
      g₀ = ⧜subst (tsy)

      fam' : Fin-R 1 -> _
      fam' x = _ , f₀ , g₀

      covers-0 : {x : 𝐂𝐭𝐱ᵘ 𝑨}
                    (h : incl _ ⟶ x) →
                    ⧜subst (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h _ (con cx tsx))) ∼ ⧜subst (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h _ (con cx tsy)))
                    ->
                    ((p : Fin-R 1) →
                    ((fst (fam' p .snd) ◆ h))
                    ∼ (snd (fam' p .snd) ◆ h))
      covers-0 h p q = cong-Str ⟨_⟩ p
        >> incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h _ (con cx tsx)) ≣ (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h _ (con cx tsy))) <<
        ⟪ cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 ⟫
        ⟪ cancel-injective-con₃ refl-≣ ⟫
        ⟪ §-reext-Terms-𝕋×.prop-2 h tsx ≀∼≀ §-reext-Terms-𝕋×.prop-2 h tsy ⟫
        ⟪ cong-Str ⧜subst ⟫
        >> (⧜subst tsx ◆ h) ∼ (⧜subst tsy ◆ h) <<

      covers-1 : {x : 𝐂𝐭𝐱ᵘ 𝑨}
                    (h : incl _ ⟶ x) →
                    ((p : Fin-R 1) →
                    ((fst (fam' p .snd) ◆ h))
                    ∼ (snd (fam' p .snd) ◆ h))
                    ->
                    ⧜subst (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h _ (con cx tsx))) ∼ ⧜subst (incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 h _ (con cx tsy)))
      covers-1 h p = p (zero)
        >> (⧜subst tsx ◆ h) ∼ (⧜subst tsy ◆ h) <<
        ⟪ cong-Str ⟨_⟩ ⟫
        ⟪ §-reext-Terms-𝕋×.prop-2 h tsx ⁻¹ ≀∼≀ §-reext-Terms-𝕋×.prop-2 h tsy ⁻¹ ⟫
        ⟪ cong-Str (con cx) ⟫
        ⟪ cong-Str incl ⟫
        ⟪ cong-Str ⧜subst ⟫


