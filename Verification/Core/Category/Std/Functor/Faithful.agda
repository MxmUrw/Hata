
module Verification.Core.Category.Std.Functor.Faithful where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Set.Setoid.Morphism



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isFaithful (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field {{isInjective:map}} : ∀{a b : ⟨ 𝒞 ⟩} -> isInjective (map {{of F}} {a} {b})

  open isFaithful {{...}} public


module _ {D : 𝒰 𝑙} {{_ : isCategory {𝑙₁} D}}
  {A : 𝒰 𝑖} (Hom' : A -> A -> 𝒰 𝑗)
  {{_ : ∀{a b : A} -> isSetoid {𝑘} (Hom' a b)}}
  (id' : ∀{a : A} -> Hom' a a)
  (_◆'_ : ∀{a b c : A} -> Hom' a b -> Hom' b c -> Hom' a c)
  (ϕ : A -> D)
  (map-ϕ : ∀{a b : A} -> Hom' a b -> ϕ a ⟶ ϕ b)
  {{_ : ∀{a b : A} -> isSetoidHom ′ Hom' a b ′ (ϕ a ⟶ ϕ b) (map-ϕ {a} {b})}}
  {{_ : ∀{a b : A} -> isInjective (map-ϕ {a} {b})}}
  (functoriality-◆' : ∀{a b c : A} -> {f : Hom' a b} {g : Hom' b c} -> map-ϕ (f ◆' g) ∼ map-ϕ f ◆ map-ϕ g)
  (functoriality-id' : ∀{a : A} -> map-ϕ (id' {a}) ∼ id)
  where

  abstract
    private
      lem-1 : ∀{a b : A} {f : Hom' a b} -> (id' ◆' f) ∼ f
      lem-1 {f = f} = cancel-injective $
              map-ϕ (id' ◆' f)         ⟨ functoriality-◆' ⟩-∼
              map-ϕ id' ◆ map-ϕ f      ⟨ functoriality-id' ◈ refl ⟩-∼
              id ◆ map-ϕ f             ⟨ unit-l-◆ ⟩-∼
              map-ϕ f                  ∎

      lem-2 : ∀{a b : A} {f : Hom' a b} -> (f ◆' id') ∼ f
      lem-2 {f = f} = cancel-injective $
              map-ϕ (f ◆' id')         ⟨ functoriality-◆' ⟩-∼
              map-ϕ f ◆ map-ϕ id'      ⟨ refl ◈ functoriality-id' ⟩-∼
              map-ϕ f ◆ id             ⟨ unit-r-◆ ⟩-∼
              map-ϕ f                  ∎

      lem-3 : ∀{a b c d : A} {f : Hom' a b} {g : Hom' b c} {h : Hom' c d} -> ((f ◆' g) ◆' h) ∼ (f ◆' (g ◆' h))
      lem-3 {f = f} {g} {h} = cancel-injective $
              map-ϕ ((f ◆' g) ◆' h)            ⟨ functoriality-◆' ⟩-∼
              map-ϕ (f ◆' g) ◆ map-ϕ h         ⟨ functoriality-◆' ◈ refl ⟩-∼
              (map-ϕ f ◆ map-ϕ g) ◆ map-ϕ h    ⟨ assoc-l-◆ ⟩-∼
              map-ϕ f ◆ (map-ϕ g ◆ map-ϕ h)    ⟨ refl ◈ functoriality-◆' ⁻¹ ⟩-∼
              map-ϕ f ◆ map-ϕ (g ◆' h)         ⟨ functoriality-◆' ⁻¹ ⟩-∼
              map-ϕ (f ◆' (g ◆' h))            ∎

      lem-4 : ∀{a b c : A} {f g : Hom' a b} {h i : Hom' b c}
              -> (f ∼ g) -> (h ∼ i)
              -> (f ◆' h) ∼ (g ◆' i)
      lem-4 {f = f} {g} {h} {i} p q = cancel-injective $
              map-ϕ (f ◆' h)    ⟨ functoriality-◆' ⟩-∼
              map-ϕ f ◆ map-ϕ h ⟨ cong-∼ p ◈ cong-∼ q ⟩-∼
              map-ϕ g ◆ map-ϕ i ⟨ functoriality-◆' ⁻¹ ⟩-∼
              map-ϕ (g ◆' i)    ∎

  isCategory:byFaithful : isCategory A
  isCategory.Hom isCategory:byFaithful = Hom'
  isCategory.isSetoid:Hom isCategory:byFaithful = it
  isCategory.id isCategory:byFaithful = id'
  isCategory._◆_ isCategory:byFaithful = _◆'_
  isCategory.unit-l-◆ isCategory:byFaithful = lem-1
  isCategory.unit-r-◆ isCategory:byFaithful = lem-2
  isCategory.unit-2-◆ isCategory:byFaithful = lem-1
  isCategory.assoc-l-◆ isCategory:byFaithful = lem-3
  isCategory.assoc-r-◆ isCategory:byFaithful = lem-3 ⁻¹
  isCategory._◈_ isCategory:byFaithful = lem-4




