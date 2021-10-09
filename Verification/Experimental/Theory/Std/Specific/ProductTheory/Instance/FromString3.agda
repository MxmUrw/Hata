
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString3 where

open import Verification.Conventions hiding (_⊔_ ; lookup)
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
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromANVecTree
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.DirectCheck

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries
-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.ToCheckTree2


ι-ℕ-人ℕ : ℕ -> 人ℕ
ι-ℕ-人ℕ zero = ◌
ι-ℕ-人ℕ (suc n) = incl tt ⋆ ι-ℕ-人ℕ n

ι-Fin-R-[]ᶠ : ∀{n} -> Fin-R n -> [ ι-ℕ-人ℕ n ]ᶠ
ι-Fin-R-[]ᶠ zero = tt , left-∍ incl
ι-Fin-R-[]ᶠ (suc i) = ι-Fin-R-[]ᶠ i .fst , right-∍ (ι-Fin-R-[]ᶠ i .snd)

module _ {𝒯 : ProductTheory ℓ₀} {{_ : IShow (Sort 𝒯)}} {{Def : TokenDefinition (UntypedCon 𝒯)}} where



  -----------------------------------------
  -- the checking

  mutual
    TreesToVecTrees : ∀{m n} -> List (Tree (UntypedCon 𝒯) (Fin-R n)) -> String + (Vec (VecTree1 (Node 𝒯 (ι-ℕ-人ℕ n)) (size× 𝒯)) m)
    TreesToVecTrees {m = zero} ⦋⦌ = right ⦋⦌
    TreesToVecTrees {m = zero} (x ∷ ts) = left $ "too many arguments "
    TreesToVecTrees {m = suc m} ⦋⦌ = left $ "too few arguments"
    TreesToVecTrees {m = suc m} (t ∷ ts) = do
      t' <- TreeToVecTree t
      ts' <- TreesToVecTrees ts
      return (t' ∷ ts')

    TreeToVecTree : ∀{n} -> Tree (UntypedCon 𝒯) (Fin-R n) -> String + (VecTree1 (Node 𝒯 (ι-ℕ-人ℕ n)) (size× 𝒯))
    TreeToVecTree (Tree.node x ts) = do
      ts' <- TreesToVecTrees ts
      return ((node1 (isNode x) ts'))
    TreeToVecTree (var x) = right (node1 (isVar (ι-Fin-R-[]ᶠ x)) ⦋⦌)

  TreeToADAN : Tree (UntypedCon 𝒯) String -> String + (∑ λ n -> VecTree1 (Node 𝒯 n) (size× 𝒯))
  TreeToADAN t = do
    let uc , t1 = renameFreeVariables (0 , emptyC) t
    t2 <- either (const (left "Could not finitize vars")) right (finitizeFreeVariables uc t1)
    t3 <- TreeToVecTree t2
    return (_ , t3)

  𝑹 = (∑ λ xs -> ∑ λ x -> Term₁-𝕋× (𝒯) xs x)

  ProductTheory:fromString : String -> String + (𝑹 ^ 2)
  ProductTheory:fromString s = do
    t1 , t2 <- parseTwolines Def s
    _ , t1' <- TreeToADAN t1
    _ , t2' <- TreeToADAN t2
    let _ , t1ini = makeInitialTree t1'
    _ , _ , t1fin <- makeFinalTree t1ini
    -- let t1term = constructTerm 𝒯 t1fin
    {!!}


