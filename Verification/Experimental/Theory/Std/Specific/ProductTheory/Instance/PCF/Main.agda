
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
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
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
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF.Base


module _ {𝑨 : 𝕋× 𝑖} where

  ∂-𝕋× : ∀{x y : 𝐂𝐭𝐱 𝑨} -> (t : Pair x y) -> (isBase-𝕋× t +-𝒰 (∑ λ n -> isSplittableC (𝐂𝐭𝐱 𝑨) n t SplitP))
  ∂-𝕋× (◌-⧜ , ◌-⧜) = left isBase:⊥
  ∂-𝕋× {x} {y} ((f₀ ⋆-⧜ f₁) , (g₀ ⋆-⧜ g₁)) = right (2 , record { famC = fam' ; coversC = {!!} ; fampropsC = {!!} })
    where
      fam' : 2 ∍ tt -> ∑ λ x' -> Pair x' y
      fam' (right-∍ i) = _ , f₀ , g₀
      fam' (left-∍ i) = _ , f₁ , g₁
  ∂-𝕋× (incl (var x) , incl (var y)) with x ≟-Str y
  ... | yes refl-≣ = left isBase:id
  ... | no ¬p = left (isBase:var _ _ ¬p)
  ∂-𝕋× (incl (var x) , incl (con c x₁)) = {!!}
  ∂-𝕋× (incl (con c x) , incl (var x₁)) = {!!}
  ∂-𝕋× (incl (con {αs = αsx} cx tsx) , incl (con {αs = αsy} cy tsy)) with αsx ≟-Str αsy
  ... | no ¬p = {!!}
  ... | yes refl-≣ with cx ≟-Str cy
  ... | no ¬p = {!!}
  ... | yes refl-≣ = right (1 , record { famC = fam' ; coversC = {!!} ; fampropsC = {!!} })
    where
      f₀ = inverse-◆ (of retro-Terms-𝕋×) (tsx)
      g₀ = inverse-◆ (of retro-Terms-𝕋×) (tsy)

      fam' : 1 ∍ tt -> _
      fam' x = _ , f₀ , g₀

