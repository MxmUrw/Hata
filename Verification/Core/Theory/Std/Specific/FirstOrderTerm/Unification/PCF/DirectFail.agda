
{-# OPTIONS --experimental-lossy-unification #-}
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.DirectFail where

open import Verification.Conventions hiding (Structure)

-- open import Verification.Core.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Misc
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.VariantTranslation.Definition
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
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Property.Base
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Reflection
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Preservation
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
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad



module _ {Σ : 𝒯FOSignature 𝑖} where
  cancel-injective-con : ∀{αsx αsy α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {c : Con Σ αsx α} {d : Con Σ αsy α}
                         {tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩)}
                         {tsy : 𝒯⊔Terms Σ ((ι αsy)) (⟨ Γ ⟩)}
                         -> 𝒯⊔Term.con c tsx ≣ con d tsy
                         -> αsx ≣ αsy
  cancel-injective-con refl-≣ = refl-≣

  module _ {αsx αsy α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} (c : Con Σ αsx α) (d : Con Σ αsy α)
                     (tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩))
                     (tsy : 𝒯⊔Terms Σ ((ι αsy)) (⟨ Γ ⟩))
                     (¬p : ¬ (αsx ≣ αsy))
           where

    private
      module _ {Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {{_ : isCoequalizerCandidate (map (⧜subst (incl (con c tsx)))) (map (⧜subst (incl (con d tsy)))) (ι Γ')}} where

        π' : incl (incl ⟨ Γ ⟩) ⟶ ι Γ'
        π' = π₌?

        lem-1   : con c (reext-𝒯⊔Terms ⟨ π' ⟩ tsx) ≣
                  con d (reext-𝒯⊔Terms ⟨ π' ⟩ tsy)
        lem-1 = ≡→≡-Str ((funExt⁻¹ (⟨ equate-π₌? ⟩ _)) incl)

        lem-2 : 𝟘-𝒰
        lem-2 = ¬p (cancel-injective-con lem-1)

    hasNoCoequalizerCandidate:byCon : ¬ (hasCoequalizerCandidate {𝒞 = ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} (⧜subst (incl (con c tsx)) , ⧜subst (incl (con d tsy))))
    hasNoCoequalizerCandidate:byCon P = lem-2 {Γ' = Γ'}
      where
        Γ' = ⟨ P ⟩

        instance
          P' = isCoequalizerCandidate:byEquivalence (of P)



  cancel-injective-con₂ : ∀{αsx αsy α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {c : Con Σ αsx α} {d : Con Σ αsy α}
                         {tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩)}
                         {tsy : 𝒯⊔Terms Σ ((ι αsy)) (⟨ Γ ⟩)}
                         -> (p : αsx ≣ αsy)
                         -> 𝒯⊔Term.con c tsx ≣ con d tsy
                         -> transport-Str (cong-Str (λ ξ -> Con Σ ξ α) p) c ≣ d
  cancel-injective-con₂ p refl-≣ with isset-Str p refl-≣
  ... | refl-≣ = refl-≣


  cancel-injective-con₃ : ∀{αsx αsy α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {c : Con Σ αsx α} {d : Con Σ αsy α}
                         {tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩)}
                         {tsy : 𝒯⊔Terms Σ ((ι αsy)) (⟨ Γ ⟩)}
                         -> (p : αsx ≣ αsy)
                         -> 𝒯⊔Term.con c tsx ≣ con d tsy
                         -> transport-Str (cong-Str (λ ξ -> 𝒯⊔Terms Σ ((ι ξ)) (⟨ Γ ⟩)) p) tsx ≣ tsy
  cancel-injective-con₃ p refl-≣ with isset-Str p refl-≣
  ... | refl-≣ = refl-≣

  -- cancel-injective-incl-Terms : {Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× Σ)} {Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× Σ)}
  --                          -> {f g : 𝑒𝑙 ⟨ Γ ⟩ ⟶ (Term-𝕋× Σ Δ)}
  --                          -> incl-Terms f ≣ incl-Terms g
  --                          -> f ∼ g
  -- cancel-injective-incl-Terms = {!!}

  module _ {αsx α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} (c : Con Σ αsx α) (d : Con Σ αsx α)
            (tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩))
            (tsy : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩))
            (¬p : ¬ (c ≣ d)) where

    private
      module _ {Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {{_ : isCoequalizerCandidate (map (⧜subst (incl (con c tsx)))) (map (⧜subst (incl (con d tsy)))) (ι Γ')}} where

        π' : incl (incl ⟨ Γ ⟩) ⟶ ι Γ'
        π' = π₌?

        lem-1   : con c (reext-𝒯⊔Terms ⟨ π' ⟩ tsx) ≣
                  con d (reext-𝒯⊔Terms ⟨ π' ⟩ tsy)
        lem-1 = ≡→≡-Str ((funExt⁻¹ (⟨ equate-π₌? ⟩ _)) incl)

        lem-2 : 𝟘-𝒰
        lem-2 = ¬p (cancel-injective-con₂ refl-≣ lem-1)

    hasNoCoequalizerCandidate:byCon₂ : ¬ (hasCoequalizerCandidate {𝒞 = ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} (⧜subst (incl (con c tsx)) , ⧜subst (incl (con d tsy))))
    hasNoCoequalizerCandidate:byCon₂ P = lem-2 {Γ' = Γ'}
      where
        Γ' = ⟨ P ⟩

        instance
          P' = isCoequalizerCandidate:byEquivalence (of P)


