
module Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.PCF.DirectFail where

open import Verification.Conventions hiding (Structure)

-- open import Verification.Core.Conventions hiding (Structure ; isSetoid:byPath)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.Monoid.Free.Element
-- open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Everything -- hiding (isSetoid:Function)
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

open import Verification.Core.Data.List.Variant.Base.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Definition
open import Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Instance.FormalSystem


module _ {𝑨 : 𝕋× 𝑖} where
  cancel-injective-con : ∀{αsx αsy α} {Γ : 𝐂𝐭𝐱 𝑨} {c : Con 𝑨 αsx α} {d : Con 𝑨 αsy α}
                         {tsx : Terms-𝕋× 𝑨 (incl (ι αsx)) (incl ⟨ Γ ⟩)}
                         {tsy : Terms-𝕋× 𝑨 (incl (ι αsy)) (incl ⟨ Γ ⟩)}
                         -> con c tsx ≣ con d tsy
                         -> αsx ≣ αsy
  cancel-injective-con refl-≣ = refl-≣

  module _ {αsx αsy α} {Γ : 𝐂𝐭𝐱 𝑨} (c : Con 𝑨 αsx α) (d : Con 𝑨 αsy α)
                     (tsx : Terms-𝕋× 𝑨 (incl (ι αsx)) (incl ⟨ Γ ⟩))
                     (tsy : Terms-𝕋× 𝑨 (incl (ι αsy)) (incl ⟨ Γ ⟩))
                     (¬p : ¬ (αsx ≣ αsy))
           where

    private
      module _ {Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} {{_ : isCoequalizerCandidate (map (⧜subst (incl (con c tsx)))) (map (⧜subst (incl (con d tsy)))) (ι Γ')}} where

        π' : ι (incl ⟨ Γ ⟩) ⟶ ι Γ'
        π' = π₌?

        lem-1   : con c (reext-Terms-𝕋× ⟨ π' ⟩ tsx) ≣
                  con d (reext-Terms-𝕋× ⟨ π' ⟩ tsy)
        lem-1 = ≡→≡-Str ((funExt⁻¹ (⟨ equate-π₌? ⟩ _)) incl)

        lem-2 : 𝟘-𝒰
        lem-2 = ¬p (cancel-injective-con lem-1)

    hasNoCoequalizerCandidate:byCon : ¬ (hasCoequalizerCandidate {X = 𝐂𝐭𝐱 𝑨} (⧜subst (incl (con c tsx)) , ⧜subst (incl (con d tsy))))
    hasNoCoequalizerCandidate:byCon P = lem-2 {Γ' = Γ'}
      where
        Γ' = ⟨ P ⟩

        instance
          P' = isCoequalizerCandidate:byEquivalence (of P)



  cancel-injective-con₂ : ∀{αsx αsy α} {Γ : 𝐂𝐭𝐱 𝑨} {c : Con 𝑨 αsx α} {d : Con 𝑨 αsy α}
                         {tsx : Terms-𝕋× 𝑨 (incl (ι αsx)) (incl ⟨ Γ ⟩)}
                         {tsy : Terms-𝕋× 𝑨 (incl (ι αsy)) (incl ⟨ Γ ⟩)}
                         -> (p : αsx ≣ αsy)
                         -> con c tsx ≣ con d tsy
                         -> transport-Str (cong-Str (λ ξ -> Con 𝑨 ξ α) p) c ≣ d
  cancel-injective-con₂ p refl-≣ with isset-Str p refl-≣
  ... | refl-≣ = refl-≣


  cancel-injective-con₃ : ∀{αsx αsy α} {Γ : 𝐂𝐭𝐱 𝑨} {c : Con 𝑨 αsx α} {d : Con 𝑨 αsy α}
                         {tsx : Terms-𝕋× 𝑨 (incl (ι αsx)) (incl ⟨ Γ ⟩)}
                         {tsy : Terms-𝕋× 𝑨 (incl (ι αsy)) (incl ⟨ Γ ⟩)}
                         -> (p : αsx ≣ αsy)
                         -> con c tsx ≣ con d tsy
                         -> transport-Str (cong-Str (λ ξ -> Terms-𝕋× 𝑨 (incl (ι ξ)) (incl ⟨ Γ ⟩)) p) tsx ≣ tsy
  cancel-injective-con₃ p refl-≣ with isset-Str p refl-≣
  ... | refl-≣ = refl-≣

  -- cancel-injective-incl-Terms : {Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)} {Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)}
  --                          -> {f g : 𝑒𝑙 ⟨ Γ ⟩ ⟶ (Term-𝕋× 𝑨 Δ)}
  --                          -> incl-Terms f ≣ incl-Terms g
  --                          -> f ∼ g
  -- cancel-injective-incl-Terms = {!!}

  module _ {αsx α} {Γ : 𝐂𝐭𝐱 𝑨} (c : Con 𝑨 αsx α) (d : Con 𝑨 αsx α)
            (tsx : Terms-𝕋× 𝑨 (incl (ι αsx)) (incl ⟨ Γ ⟩))
            (tsy : Terms-𝕋× 𝑨 (incl (ι αsx)) (incl ⟨ Γ ⟩))
            (¬p : ¬ (c ≣ d)) where

    private
      module _ {Γ' : ⧜𝐒𝐮𝐛𝐬𝐭 (Terms 𝑨)} {{_ : isCoequalizerCandidate (map (⧜subst (incl (con c tsx)))) (map (⧜subst (incl (con d tsy)))) (ι Γ')}} where

        π' : ι (incl ⟨ Γ ⟩) ⟶ ι Γ'
        π' = π₌?

        lem-1   : con c (reext-Terms-𝕋× ⟨ π' ⟩ tsx) ≣
                  con d (reext-Terms-𝕋× ⟨ π' ⟩ tsy)
        lem-1 = ≡→≡-Str ((funExt⁻¹ (⟨ equate-π₌? ⟩ _)) incl)

        lem-2 : 𝟘-𝒰
        lem-2 = ¬p (cancel-injective-con₂ refl-≣ lem-1)

    hasNoCoequalizerCandidate:byCon₂ : ¬ (hasCoequalizerCandidate {X = 𝐂𝐭𝐱 𝑨} (⧜subst (incl (con c tsx)) , ⧜subst (incl (con d tsy))))
    hasNoCoequalizerCandidate:byCon₂ P = lem-2 {Γ' = Γ'}
      where
        Γ' = ⟨ P ⟩

        instance
          P' = isCoequalizerCandidate:byEquivalence (of P)


