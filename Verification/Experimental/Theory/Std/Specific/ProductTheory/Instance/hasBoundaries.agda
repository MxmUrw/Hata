
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries where

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
-- open import Verification.Experimental.Theory.Std.Presentation.CheckTree.Definition2



module _ {A : 𝒰 𝑖} {R : 人List A -> A -> 𝒰 𝑖} where
  π₀-⋆-⧜ : ∀{as0 as1 bs : 人List A} -> CtxHom R (as0 ⋆ as1) bs -> CtxHom R as0 bs
  π₀-⋆-⧜ (f ⋆-⧜ g) = f

  π₁-⋆-⧜ : ∀{as0 as1 bs : 人List A} -> CtxHom R (as0 ⋆ as1) bs -> CtxHom R as1 bs
  π₁-⋆-⧜ (f ⋆-⧜ g) = g


ι-Fin-R : Fin-R n -> ℕ
ι-Fin-R zero = zero
ι-Fin-R (suc m) = suc (ι-Fin-R m)

instance
  IShow:Fin-R : IShow (Fin-R n)
  IShow:Fin-R = record { show = λ x → show (ι-Fin-R x) }

UntypedCon : ProductTheory 𝑖 -> 𝒰 _
UntypedCon 𝒯 = ∑ λ xs -> ∑ λ x -> Con 𝒯 xs x


module _ (𝒯 : ProductTheory ℓ₀) {{_ : IShow (Sort 𝒯)}} where

  -----------------------------------------
  -- nodes of the NGraph
  data Node (n : 人ℕ) : 𝒰₀ where
    isNode : UntypedCon 𝒯 -> Node n
    isVar :  [ n ]ᶠ -> Node n

  -- l' : UntypedCon 𝒯 -> 人ℕ
  -- l' (τs , τ , _) = map (const tt) (ι τs)

  -- size' : ∀{n} -> Node n -> 人ℕ
  -- size' (isNode n) = l' n
  -- size' (isVar x) = ◌

  -- data Node (n : 人ℕ) : 𝒰₀ where
  --   isTop : Node n
  --   notTop : Node n -> Node n

  size× : ∀{n} -> Node n -> ℕ
  size× (isNode (τs , τ , c)) = length τs
  size× (isVar x) = 0
  -- size (notTop x) = suc size x
  -- size isTop = incl tt

  -----------------------------------------
  -- the category of sorts and substitutions

  data SortTermᵈ (n : 人ℕ) : 𝒰₀ where
    var : [ n ]ᶠ -> SortTermᵈ n
    con : Sort 𝒯 -> SortTermᵈ n

  SortTermᵘ : 𝐅𝐢𝐧𝐈𝐱 (⊤-𝒰 {ℓ₀}) -> 𝐈𝐱 (⊤-𝒰 {ℓ₀}) (𝐔𝐧𝐢𝐯 ℓ₀)
  SortTermᵘ a = indexed (λ _ → SortTermᵈ ⟨ a ⟩)

  macro SortTerm = #structureOn SortTermᵘ

  instance
    isFunctor:SortTerm : isFunctor (𝐅𝐢𝐧𝐈𝐱 ⊤-𝒰) (𝐈𝐱 ⊤-𝒰 (𝐔𝐧𝐢𝐯 ℓ₀)) SortTerm
    isFunctor.map isFunctor:SortTerm = {!!}
    isFunctor.isSetoidHom:map isFunctor:SortTerm = {!!}
    isFunctor.functoriality-id isFunctor:SortTerm = {!!}
    isFunctor.functoriality-◆ isFunctor:SortTerm = {!!}

  instance
    isRelativeMonad:SortTerm : isRelativeMonad (𝑓𝑖𝑛 ⊤-𝒰) SortTerm
    isRelativeMonad.repure isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reext isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reunit-l isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:SortTerm = {!!}
    isRelativeMonad.reassoc isRelativeMonad:SortTerm = {!!}

  macro
    ℬ× : SomeStructure
    ℬ× = #structureOn (InductiveSubstitution SortTerm)

  F× : 人ℕ -> Functor ℬ× (𝐔𝐧𝐢𝐯 ℓ₀)
  F× n = f since {!!}
    where
      f : ℬ× -> 𝐔𝐧𝐢𝐯 ℓ₀
      f b = (incl (n ⋆ incl tt) ⟶ b)

  makeSort : SortTermᵈ ◌ -> Sort 𝒯
  makeSort (con x) = x

{-
  module §-SortTerm where
    prop-1 : ∀{n : 人ℕ} -> n ∼ ◌ -> SortTermᵈ n -> Sort 𝒯
    prop-1 {n} n∼◌ (var (a , x)) = impossible p4
      where
        p1 : el n ≅ el ◌
        p1 = cong-∼ n∼◌

        p2 : ix (el n) a
        p2 = x

        p3 : ix (el ◌) a
        p3 = ⟨ p1 ⟩ a p2

        p4 : 𝟘-𝒰
        p4 with p3
        ... | ()

    prop-1 {n} n∼◌ (con x) = x

    prop-2 : ∀{m n : 人ℕ} -> n ∼ ◌ -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> 人List (Sort 𝒯) × Sort 𝒯
    prop-2 n∼◌ (f ⋆-⧜ incl x) = map (prop-1 n∼◌) f' , (prop-1 n∼◌ x)
      where
        f' = §-⧜𝐒𝐮𝐛𝐬𝐭-⊤.prop-1 {T = SortTerm} (f)

  getCtx : ∀{m n : 人ℕ} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> 人List (SortTermᵈ n)
  -- [ m ]ᶠ -> SortTermᵈ n
  getCtx s = asList (π₀-⋆-⧜ s)

  getRet : ∀{m n : 人ℕ} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = SortTerm} (incl (m ⋆ incl tt)) (incl n) -> SortTermᵈ n
  getRet (f ⋆-⧜ incl g) = g

  makeSort : SortTermᵈ ◌ -> Sort 𝒯
  makeSort (con x) = x
-}
