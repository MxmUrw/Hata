
module Verification.Core.Data.Indexed.Duplicate where

open import Verification.Core.Conventions

open import Verification.Core.Algebra.Monoid.Free.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Functor.Adjoint.Property.Preservation

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer.Preservation


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

-- we have 人List A ≅ List A
-- just as 人ℕ ≅ ℕ
-- (but both in 𝐒𝐭𝐝)

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteProducts 𝒞}} {A : 𝒰 𝑗} where

  ⨅ᶠᵘ : ∀{n : Free-𝐌𝐨𝐧 A} -> 𝐈𝐱 [ n ]ᶠ 𝒞 -> ⟨ 𝒞 ⟩
  ⨅ᶠᵘ {incl a} x = ix x (a , incl)
  ⨅ᶠᵘ {n ⋆-⧜ m} a = ⨅ᶠᵘ {n} (写* leftᶠ a) ⊓ ⨅ᶠᵘ {m} (写* rightᶠ a)
  ⨅ᶠᵘ {◌-⧜} a = ⊤

  module _ {n : 人List A} where
    macro ⨅ᶠ = #structureOn (⨅ᶠᵘ {n})

  map-⨅ᶠ : ∀{n} -> {a b : 𝐈𝐱 [ n ]ᶠ 𝒞} -> (f : a ⟶ b) -> ⨅ᶠ a ⟶ ⨅ᶠ b
  map-⨅ᶠ {incl x} {a} {b} f = f (x , incl)
  map-⨅ᶠ {n ⋆-⧜ m} {a} {b} f = map-⊓ (map-⨅ᶠ (map-写* leftᶠ {a = a} f) , map-⨅ᶠ (map-写* rightᶠ {a = a} f))
  map-⨅ᶠ {◌-⧜} {a} {b} f = intro-⊤


  instance
    isFunctor:⨅ᶠ : ∀{n} -> isFunctor (𝐈𝐱 [ n ]ᶠ 𝒞) 𝒞 ⨅ᶠ
    isFunctor.map isFunctor:⨅ᶠ = map-⨅ᶠ
    isFunctor.isSetoidHom:map isFunctor:⨅ᶠ = {!!}
    isFunctor.functoriality-id isFunctor:⨅ᶠ = {!!}
    isFunctor.functoriality-◆ isFunctor:⨅ᶠ = {!!}

  adj-写 : ∀{n} -> ∀ a -> 写 (⨅ᶠ {n} a) ⟶ a
  adj-写 {incl x} a = λ {(x , incl) → id}
  adj-写 {n ⋆-⧜ m} a (_ , left-∍ i) = π₀ ◆ adj-写 _ (_ , i)
  adj-写 {n ⋆-⧜ m} a (_ , right-∍ i) = π₁ ◆ adj-写 _ (_ , i)
  adj-写 {◌-⧜} a ()

  coadj-写 : ∀{n} -> ∀ a -> a ⟶ ⨅ᶠ {n} (写 a)
  coadj-写 {incl x} a = id
  coadj-写 {n ⋆-Free-𝐌𝐨𝐧 m} a = ⧼ coadj-写 {n} _ , coadj-写 {m} _ ⧽
  coadj-写 {◌-Free-𝐌𝐨𝐧} a = intro-⊤

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

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} {A : 𝒰 𝑗} where

  ⨆ᶠᵘ : ∀{n : 人List A} -> 𝐈𝐱 [ n ]ᶠ 𝒞 -> ⟨ 𝒞 ⟩
  ⨆ᶠᵘ {incl x} a = ix a (x , incl)
  ⨆ᶠᵘ {n ⋆-⧜ n₁} a = {!!}
  ⨆ᶠᵘ {◌-⧜} a = {!!}

  module _ {n : 人List A} where
    macro ⨆ᶠ = #structureOn (⨆ᶠᵘ {n})

  instance
    isFunctor:⨆ᶠ : ∀{n} -> isFunctor (𝐈𝐱 [ n ]ᶠ 𝒞) 𝒞 ⨆ᶠ
    isFunctor:⨆ᶠ = {!!}

--------------------------------------------------------------
-- the indexed coproduct

module _ {𝒞 : Category 𝑖} {{_ : hasIndexedCoproducts {𝑗} 𝒞}} {A : 𝒰 𝑗} where

  ⨆ᵘ : 𝐈𝐱 A 𝒞 -> ⟨ 𝒞 ⟩
  ⨆ᵘ x = ⨆ᵢ (ix x)

  macro ⨆ = #structureOn (⨆ᵘ)

  instance
    isFunctor:⨆ : isFunctor (𝐈𝐱 A 𝒞) 𝒞 ⨆
    isFunctor:⨆ = {!!}



