
module Verification.Experimental.Data.FiniteIndexed.Property.Adjunction where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Contradiction
-- open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.SeparatingFamily

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Instance.SeparatingFamily

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct
open import Verification.Experimental.Category.Std.Functor.RelativeAdjoint

open import Verification.Experimental.Data.FiniteIndexed.Definition


module _ {I J : 𝒰 𝑖} (f : I -> J) where

  ix*ᵘ : 𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖) -> 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)
  ix*ᵘ s = indexed (λ i → ix s (f i))

  macro ix* = #structureOn ix*ᵘ

  ix!ᵘ : 𝐅𝐢𝐧𝐈𝐱 I -> 𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)
  ix!ᵘ (incl s) = 𝑒𝑙 (map-Free-𝐌𝐨𝐧 f s)

  macro ix! = #structureOn ix!ᵘ

module _ {I J : 𝒰 𝑖} {f : I -> J} where
  map-ix* : ∀{a b : 𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)} -> (a ⟶ b) -> ix* f a ⟶ ix* f b
  map-ix* g = λ i → g (f i)

  instance
    isFunctor:ix* : isFunctor (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) (ix* f)
    isFunctor.map isFunctor:ix* = map-ix*
    isFunctor.isSetoidHom:map isFunctor:ix* = {!!}
    isFunctor.functoriality-id isFunctor:ix* = {!!}
    isFunctor.functoriality-◆ isFunctor:ix* = {!!}

  instance
    isFunctor:ix! : isFunctor (𝐅𝐢𝐧𝐈𝐱 I) (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)) (ix! f)
    isFunctor:ix! = {!!}

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-∍ : (f : A -> B) -> {as : Free-𝐌𝐨𝐧 A} {a : A} -> as ∍ a -> map-Free-𝐌𝐨𝐧 f as ∍ f a
  map-∍ f incl = incl
  map-∍ f (right-∍ p) = right-∍ (map-∍ f p)
  map-∍ f (left-∍ p) = left-∍ (map-∍ f p)

module _ {I J : 𝒰 𝑖} (f : I -> J) where
  -- adj-𝐅𝐢𝐧𝐈𝐱 : 

  refree-𝐅𝐢𝐧𝐈𝐱 : ∀{a : 𝐅𝐢𝐧𝐈𝐱 I} {b : 𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)} -> ι a ⟶ (ix* f b) -> ix! f a ⟶ b
  refree-𝐅𝐢𝐧𝐈𝐱 {incl (incl x)} g .(f x) incl = g x incl
  refree-𝐅𝐢𝐧𝐈𝐱 {incl (a ⋆-Free-𝐌𝐨𝐧 b)} g i (right-∍ p) = refree-𝐅𝐢𝐧𝐈𝐱 {a = incl b} ((λ _ -> right-∍) ◆ g) i p
  refree-𝐅𝐢𝐧𝐈𝐱 {incl (a ⋆-Free-𝐌𝐨𝐧 b)} g i (left-∍ p)  = refree-𝐅𝐢𝐧𝐈𝐱 {a = incl a} ((λ _ -> left-∍) ◆ g) i p
  refree-𝐅𝐢𝐧𝐈𝐱 {incl ◌-Free-𝐌𝐨𝐧} g i ()

  recofree-𝐅𝐢𝐧𝐈𝐱 : ∀{a : 𝐅𝐢𝐧𝐈𝐱 I} {b : 𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)} -> ix! f a ⟶ b -> ι a ⟶ (ix* f b)
  recofree-𝐅𝐢𝐧𝐈𝐱 {a} g i x = g (f i) (map-∍ f x)

module _ {I J : 𝒰 𝑖} {f : I -> J} where
  instance
    isRelativeAdjoint:ix!,ix* : isRelativeAdjoint ι (ix! f) (ix* f)
    isRelativeAdjoint.refree isRelativeAdjoint:ix!,ix* = refree-𝐅𝐢𝐧𝐈𝐱 f
    isRelativeAdjoint.recofree isRelativeAdjoint:ix!,ix* = recofree-𝐅𝐢𝐧𝐈𝐱 f

