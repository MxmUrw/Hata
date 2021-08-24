
module Verification.Experimental.Data.Indexed.Duplicate where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Algebra.Monoid.Free.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Functor.Adjoint.Property.Preservation

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Preservation


module _ {𝒞' : 𝒰 𝑖} {{_ : isCategory {𝑘} 𝒞'}} {I : 𝒰 𝑗} where

  private
    𝒞 : Category _
    𝒞 = ′ 𝒞' ′

  --------------------------------------------------------------
  -- the duplication / constant functor

  duplix : 𝒞' -> 𝐈𝐱 I 𝒞
  duplix x = indexed (const x)

  macro 写 = #structureOn duplix

  module _ {a b : 𝒞'} where
    map-写 : (f : a ⟶ b) -> 写 a ⟶ 写 b
    map-写 f = {!!}

  instance
    isFunctor:写 : isFunctor 𝒞 (𝐈𝐱 I 𝒞) 写
    isFunctor.map isFunctor:写 = {!!}
    isFunctor.isSetoidHom:map isFunctor:写 = {!!}
    isFunctor.functoriality-id isFunctor:写 = {!!}
    isFunctor.functoriality-◆ isFunctor:写 = {!!}


--------------------------------------------------------------
-- the proper base change functor

module _ {𝒞 : Category 𝑖} {I : 𝒰 𝑗} {J : 𝒰 𝑘} (f : I -> J) where

  写* : (𝐈𝐱 J 𝒞) -> (𝐈𝐱 I 𝒞)
  写* x = indexed λ i -> ix x (f i)

  map-写* : {a b : 𝐈𝐱 J 𝒞} -> (a ⟶ b) -> 写* a ⟶ 写* b
  map-写* g = {!!}



--------------------------------------------------------------
-- the finite product

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} where

  ⨅ᶠᵘ : ∀{n : 人ℕ} -> 𝐈𝐱 [ n ]ᶠ 𝒞 -> ⟨ 𝒞 ⟩
  ⨅ᶠᵘ {incl tt} a = ix a incl
  ⨅ᶠᵘ {n ⋆-⧜ m} a = ⨅ᶠᵘ {n} (写* left-∍ a) ⊓ ⨅ᶠᵘ {m} (写* right-∍ a)
  ⨅ᶠᵘ {◌-⧜} a = ⊤

  module _ {n : 人ℕ} where
    macro ⨅ᶠ = #structureOn (⨅ᶠᵘ {n})

  map-⨅ᶠ : ∀{n} -> {a b : 𝐈𝐱 [ n ]ᶠ 𝒞} -> (f : a ⟶ b) -> ⨅ᶠ a ⟶ ⨅ᶠ b
  map-⨅ᶠ {incl tt} {a} {b} f = f incl
  map-⨅ᶠ {n ⋆-⧜ m} {a} {b} f = map-⊓ (map-⨅ᶠ (map-写* left-∍ {a = a} f) , map-⨅ᶠ (map-写* right-∍ {a = a} f))
  map-⨅ᶠ {◌-⧜} {a} {b} f = intro-⊤


  instance
    isFunctor:⨅ᶠ : ∀{n} -> isFunctor (𝐈𝐱 [ n ]ᶠ 𝒞) 𝒞 ⨅ᶠ
    isFunctor.map isFunctor:⨅ᶠ = map-⨅ᶠ
    isFunctor.isSetoidHom:map isFunctor:⨅ᶠ = {!!}
    isFunctor.functoriality-id isFunctor:⨅ᶠ = {!!}
    isFunctor.functoriality-◆ isFunctor:⨅ᶠ = {!!}

  adj-写 : ∀{n a} -> 写 (⨅ᶠ {n} a) ⟶ a
  adj-写 {incl tt} {a} = λ {incl → id}
  adj-写 {n ⋆-⧜ m} {a} (left-∍ i) = π₀ ◆ adj-写 i
  adj-写 {n ⋆-⧜ m} {a} (right-∍ i) = π₁ ◆ adj-写 i
  adj-写 {◌-⧜} {a} ()

  coadj-写 : ∀{n a} -> a ⟶ ⨅ᶠ {n} (写 a)
  coadj-写 {incl tt} {a} = id
  coadj-写 {n ⋆-Free-𝐌𝐨𝐧 m} {a} = ⧼ coadj-写 {n} , coadj-写 {m} ⧽
  coadj-写 {◌-Free-𝐌𝐨𝐧} {a} = intro-⊤

  module _ {n} where
    instance
      isAdjoint:写,⨅ᶠ : 写 ⊣ (⨅ᶠ {n})
      isAdjoint.adj isAdjoint:写,⨅ᶠ = adj-写
      isAdjoint.coadj isAdjoint:写,⨅ᶠ = coadj-写 {n}
      isAdjoint.isNatural:adj isAdjoint:写,⨅ᶠ = {!!}
      isAdjoint.isNatural:coadj isAdjoint:写,⨅ᶠ = {!!}
      isAdjoint.reduce-coadj isAdjoint:写,⨅ᶠ = {!!}
      isAdjoint.reduce-adj isAdjoint:写,⨅ᶠ = {!!}

    instance
      preservesCoequalizers:写 : preservesCoequalizers 写
      preservesCoequalizers:写 = preservesCoequalizers:byLeftAdjoint



--------------------------------------------------------------
-- the finite coproduct

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where

  ⨆ᶠ-𝐈𝐱 : ∀{n : 人ℕ} -> 𝐈𝐱 [ n ]ᶠ 𝒞 -> ⟨ 𝒞 ⟩
  ⨆ᶠ-𝐈𝐱 {incl tt} a = ix a incl
  ⨆ᶠ-𝐈𝐱 {n ⋆-⧜ n₁} a = {!!}
  ⨆ᶠ-𝐈𝐱 {◌-⧜} a = {!!}



