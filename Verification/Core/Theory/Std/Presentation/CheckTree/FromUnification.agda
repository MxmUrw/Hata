
module Verification.Core.Theory.Std.Presentation.CheckTree.FromUnification where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Function.Surjective
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.Monoid.Free.Element
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Sum.Instance.Functor
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Merge
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.Semiring
open import Verification.Core.Computation.Unification.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Sum.Instance.Monad
open import Verification.Core.Theory.Std.Presentation.CheckTree.Definition2

record is1Category (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field ∼→≡ : ∀{a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> (f ∼ g) -> f ≡ g

open is1Category {{...}} public

module _ {𝒞 : Category 𝑖} {{_ : is1Category 𝒞}} where
  HomFᵘ : ∀(a : ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩ -> 𝐔𝐧𝐢𝐯 (𝑖 ⌄ 1)
  HomFᵘ a x = a ⟶ x

  module _ {a : ⟨ 𝒞 ⟩} where
    instance
      isFunctor:F : isFunctor 𝒞 (𝐔𝐧𝐢𝐯 (𝑖 ⌄ 1)) (HomFᵘ a)
      isFunctor.map isFunctor:F = λ f g → g ◆ f
      isFunctor.isSetoidHom:map isFunctor:F = record { cong-∼ = λ {f} {g} p i h → h ◆ ∼→≡ p i }
      isFunctor.functoriality-id isFunctor:F = funExt λ x → ∼→≡ unit-r-◆
      isFunctor.functoriality-◆ isFunctor:F = funExt λ x → ∼→≡ assoc-r-◆

  module _ (a : ⟨ 𝒞 ⟩) where
    macro HomF = #structureOn (HomFᵘ a)


module _ (𝒞 : Category 𝑖) {{_ : is1Category 𝒞}} {{_ : hasUnification 𝒞}} {{_ : hasFiniteCoproducts 𝒞}} where


  private
    tryMerge× : ∀{a} -> ∀{b0 b1 : ⟨ 𝒞 ⟩} -> (v0 : HomF a b0) (v1 : HomF a b1)
                    -> Maybe (∑ λ bx -> ∑ λ (f0 : b0 ⟶ bx) -> ∑ λ (f1 : b1 ⟶ bx) -> map f0 v0 ≡ map f1 v1)
    tryMerge× {a} {b0} {b1} v0 v1 =
      let v0' : HomF a (b0 ⊔ b1)
          v0' = v0 ◆ ι₀
          v1' : HomF a (b0 ⊔ b1)
          v1' = v1 ◆ ι₁
      in case unify v0' v1' of
          (λ x → nothing)
          λ x → let p : v0 ◆ (ι₀ ◆ π₌) ∼ v1 ◆ (ι₁ ◆ π₌)
                    p = assoc-r-◆ ∙ equate-π₌ ∙ assoc-l-◆
                in right (⟨ x ⟩ , (ι₀ ◆ π₌ , ι₁ ◆ π₌ , ∼→≡ p))

  isCheckingBoundary:byUnification : ∀{a : ⟨ 𝒞 ⟩} -> isCheckingBoundary 𝒞 (HomF a)
  isCheckingBoundary:byUnification = record { tryMerge = tryMerge× }



