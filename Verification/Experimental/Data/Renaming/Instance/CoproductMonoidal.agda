
module Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full public
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid

open import Verification.Experimental.Data.Renaming.Definition

module _ {A : 𝒰 𝑖} where

  _⋆-𝐑𝐞𝐧_ : 𝐑𝐞𝐧 A -> 𝐑𝐞𝐧 A -> 𝐑𝐞𝐧 A
  _⋆-𝐑𝐞𝐧_ a b = incl (⟨ a ⟩ ⊔ ⟨ b ⟩)

  ◌-𝐑𝐞𝐧 : 𝐑𝐞𝐧 A
  ◌-𝐑𝐞𝐧 = incl ⊥

  private
    lem-1 : ∀{a b c d : 𝐅𝐢𝐧𝐈𝐱 A} -> {ϕ : a ⟶ b} -> {ψ : c ⟶ d} -> isMono ϕ -> isMono ψ -> isMono (map-⊔ (ϕ , ψ))
    isMono.cancel-mono (lem-1 p q) {z} {α} {β} x = {!!}

  map-⋆-𝐑𝐞𝐧 : ∀{a b : (𝐑𝐞𝐧 A ×-𝒰 𝐑𝐞𝐧 A)} -> (ϕ : a ⟶ b) -> λ₋ _⋆-𝐑𝐞𝐧_ a ⟶ λ₋ _⋆-𝐑𝐞𝐧_ b
  map-⋆-𝐑𝐞𝐧 (subcathom f fp , subcathom g gp) = subcathom (map-⊔ (f , g)) (lem-1 fp gp)


  instance
    isMonoid:𝐑𝐞𝐧 : isMonoid (𝐑𝐞𝐧 A)
    isMonoid:𝐑𝐞𝐧 = record
                     { _⋆_        = _⋆-𝐑𝐞𝐧_
                     ; ◌          = ◌-𝐑𝐞𝐧
                     ; unit-l-⋆   = {!!}
                     ; unit-r-⋆   = {!!}
                     ; assoc-l-⋆  = {!!}
                     ; _`cong-⋆`_ = {!!}
                     }

  instance
    isFunctor:⋆-𝐑𝐞𝐧 : isFunctor (𝐑𝐞𝐧 A ×-𝐂𝐚𝐭 𝐑𝐞𝐧 A) (𝐑𝐞𝐧 A) (λ₋ _⋆-𝐑𝐞𝐧_)
    isFunctor.map isFunctor:⋆-𝐑𝐞𝐧              = map-⋆-𝐑𝐞𝐧
    isFunctor.isSetoidHom:map isFunctor:⋆-𝐑𝐞𝐧  = {!!}
    isFunctor.functoriality-id isFunctor:⋆-𝐑𝐞𝐧 = {!!}
    isFunctor.functoriality-◆ isFunctor:⋆-𝐑𝐞𝐧  = {!!}

  instance
    isMonoidal:𝐑𝐞𝐧 : isMonoidal (𝐑𝐞𝐧 A)
    isMonoidal.isMonoid:this isMonoidal:𝐑𝐞𝐧     = isMonoid:𝐑𝐞𝐧
    isMonoidal.isFunctor:⋆ isMonoidal:𝐑𝐞𝐧       = isFunctor:⋆-𝐑𝐞𝐧
    isMonoidal.compat-Monoidal-⋆ isMonoidal:𝐑𝐞𝐧 = {!!}







