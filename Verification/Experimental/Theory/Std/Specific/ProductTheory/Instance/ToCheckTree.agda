
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.ToCheckTree where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Function.Surjective
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Sum.Instance.Monad
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Substitution.Property.Base
open import Verification.Experimental.Theory.Std.Presentation.NGraph.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition


-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString2
open import Verification.Experimental.Theory.Std.Presentation.CheckTree.Definition2



module _ (A : 𝒰 𝑖) (l : A -> 人ℕ' 𝑖) where
  data VecTree1 : 𝒰 (𝑖) where
    node1 : (a : A) -> ([ l a ]ᶠ -> VecTree1) -> VecTree1
    -- node : (a : A) -> (人Vec VecTree (l a)) -> VecTree
    -- var  : B -> VecTree

module _ {A : 𝒰 𝑖} {l : A -> 人ℕ' 𝑖} where
  data TreeStep1 : (t s : VecTree1 A l) -> 𝒰 𝑖 where

    incl : ∀{a : A} -> (ts : ([ l a ]ᶠ -> (VecTree1 A l))) -> (i : [ l a ]ᶠ)
           -> TreeStep1 (node1 a ts) (ts i)

  data TreePath1 : (t s : VecTree1 A l) -> 𝒰 (𝑖) where
    [] : ∀{t : VecTree1 A l} -> TreePath1 t t
    step : ∀{r s t : (VecTree1 A l)} -> TreePath1 r s -> TreeStep1 s t -> TreePath1 r t


  Vertex1 : (r : VecTree1 A l) -> 𝒰 _
  Vertex1 r = ∑ TreePath1 r


module _ {A : 𝒰 𝑖} {l : A -> 人ℕ' 𝑖} {ℬ : 𝒰 𝑖} {{_ : isCategory {𝑗} ℬ}} {{_ : isSet-Str ℬ}} {F : Functor ′ ℬ ′ (𝐔𝐧𝐢𝐯 𝑙)} {{_ : isCheckingBoundary ′ ℬ ′ F}} where

  module _ (initb : A -> ℬ) where

    module _ {X : 𝒰 _} {{_ : Monoid 𝑖₁ on X}} where
      fsum : ∀{n : 人ℕ' 𝑗₁} -> ([ n ]ᶠ -> X) -> X
      fsum {n = incl x} f = f (x , incl)
      fsum {n = n ⋆-⧜ m} f = fsum (λ (_ , i) -> f (_ , left-∍ i)) ⋆ fsum (λ (_ , i) -> f (_ , right-∍ i))
      fsum {n = ◌-⧜} f = ◌

    ibounds : VecTree1 A l -> 人List ℬ
    ibounds (node1 a x) = incl (initb a) ⋆ fsum (λ i -> ibounds (x i))

    makeStrategy : (v : VecTree1 A l) -> Strategy (ibounds v)
    makeStrategy (node1 a x) = {!!}




