
{-# OPTIONS --experimental-lossy-unification #-}

module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Base where

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
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Property.Sized
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Reflection
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


open import Verification.Core.Computation.Unification.Categorical.PrincipalFamilyCat

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Var
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Occur
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.OccurFail
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.DirectFail
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Size




module _ {Σ : 𝒯FOSignature 𝑖} where


  data isBase-𝕋× : ∀{x y : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> HomPair x y -> 𝒰 𝑖 where
    isBase:⊥ : ∀{x : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> {f g : ⊥ ⟶ x} -> isBase-𝕋× (f , g)
    isBase:sym : ∀{x y : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> {f g : x ⟶ y} -> isBase-𝕋× (f , g) -> isBase-𝕋× (g , f)
    isBase:id : ∀{x y : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> {f : x ⟶ y} -> isBase-𝕋× (f , f)
    isBase:var : ∀{s : Sort Σ} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} (x y : ⟨ Γ ⟩ ∍ s) -> (y ≠-∍ x) -> isBase-𝕋× (⧜subst (incl (var x)) , ⧜subst (incl (var y)))
    isBase:con-var : ∀{s : Sort Σ} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)}
                     -> ∀{αs} -> (c : Con Σ αs s) -> (ts : 𝒯⊔Terms Σ ((ι αs)) (⟨ Γ ⟩)) -> (x : ⟨ Γ ⟩ ∍ s) -> isBase-𝕋× (⧜subst (incl (con c ts)) , ⧜subst (incl (var x)))
    isBase:con≠con : ∀{αsx αsy α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)}-> (c : Con Σ αsx α) (d : Con Σ αsy α)
                     -> (tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩))
                     -> (tsy : 𝒯⊔Terms Σ ((ι αsy)) (⟨ Γ ⟩))
                     -> ¬ (αsx ≣ αsy)
                     -> isBase-𝕋× (⧜subst (incl (con c tsx)) , ⧜subst (incl (con d tsy)))

    isBase:con≠con₂ : ∀{αsx α} {Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)}-> (c : Con Σ αsx α) (d : Con Σ αsx α)
                     -> (tsx : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩))
                     -> (tsy : 𝒯⊔Terms Σ ((ι αsx)) (⟨ Γ ⟩))
                     -> ¬ (c ≣ d)
                     -> isBase-𝕋× (⧜subst (incl (con c tsx)) , ⧜subst (incl (con d tsy)))


  -- postulate
  --   size-𝕋× : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> Pair a b -> 𝒲-𝕋×

  -- SplitP : IxC (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)) -> IxC (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)) -> 𝒰₀
  -- SplitP (_ , _ , i) = (λ (_ , _ , j) -> size-𝕋× j ≪-𝒲-𝕋× size-𝕋× i)




  decide-Base-𝕋× : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} -> ∀(f g : a ⟶ b) -> isBase-𝕋× (f , g) -> hasSizedCoequalizerDecision (f , g)
  decide-Base-𝕋× f g isBase:⊥ = right (hasSizedCoequalizer:byInitial)
  decide-Base-𝕋× f g (isBase:sym p) with decide-Base-𝕋× g f p
  ... | left ¬p = left $ λ q -> ¬p (hasCoequalizerCandidate:bySym q)
  ... | right p = right (hasSizedCoequalizer:bySym p)
  decide-Base-𝕋× f .f isBase:id = right (hasSizedCoequalizer:byId)
  decide-Base-𝕋× .(⧜subst (incl (var x))) .(⧜subst (incl (var y))) (isBase:var {s} {Γ} x y y≠x) = right (hasSizedCoequalizer:varvar x y y≠x)
  decide-Base-𝕋× f g (isBase:con-var c ts v) with isFreeVar (con c ts) v
  ... | left ¬occ = right (hasSizedCoequalizer:byNoOccur (con c ts) v ¬occ)
  ... | just occ  = left (hasNoCoequalizerCandidate:byOccur (con c ts) v occ refl)
  decide-Base-𝕋× (⧜subst (incl (con c tsx))) (⧜subst (incl (con d tsy))) (isBase:con≠con .c .d .tsx .tsy p)  = left (hasNoCoequalizerCandidate:byCon  c d tsx tsy p)
  decide-Base-𝕋× (⧜subst (incl (con c tsx))) (⧜subst (incl (con d tsy))) (isBase:con≠con₂ .c .d .tsx .tsy p) = left (hasNoCoequalizerCandidate:byCon₂ c d tsx tsy p)



