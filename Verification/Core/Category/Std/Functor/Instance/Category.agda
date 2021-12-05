
module Verification.Core.Category.Std.Functor.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category


module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  macro 𝐅𝐮𝐧𝐜 = #structureOn (Functor 𝒞 𝒟)

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where

  id-𝐅𝐮𝐧𝐜 : ∀{F : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> Natural F F
  id-𝐅𝐮𝐧𝐜 {F} = id _ since natural lem-1
    where
      lem-1 : ∀{x y : ⟨ 𝒞 ⟩} (f : x ⟶ y) -> id ◆ map f ∼ map f ◆ id
      lem-1 f = unit-l-◆ ∙ unit-r-◆ ⁻¹

  _◆-𝐅𝐮𝐧𝐜_ : ∀{F G H : 𝐅𝐮𝐧𝐜 𝒞 𝒟} -> Natural F G -> Natural G H -> Natural F H
  _◆-𝐅𝐮𝐧𝐜_ α β = (λ x -> ⟨ α ⟩ x ◆ ⟨ β ⟩ x) since natural lem-1
    where
      lem-1 : ∀{x y : ⟨ 𝒞 ⟩} (f : x ⟶ y) -> (⟨ α ⟩ _ ◆ ⟨ β ⟩ _) ◆ map f ∼ map f ◆ (⟨ α ⟩ _ ◆ ⟨ β ⟩ _)
      lem-1 f = (⟨ α ⟩ _ ◆ ⟨ β ⟩ _) ◆ map f    ⟨ assoc-l-◆ ⟩-∼
                ⟨ α ⟩ _ ◆ (⟨ β ⟩ _ ◆ map f)    ⟨ refl ◈ naturality f ⟩-∼
                ⟨ α ⟩ _ ◆ (map f ◆ ⟨ β ⟩ _)    ⟨ assoc-r-◆ ⟩-∼
                (⟨ α ⟩ _ ◆ map f) ◆ ⟨ β ⟩ _    ⟨ naturality f ◈ refl ⟩-∼
                (map f ◆ ⟨ α ⟩ _) ◆ ⟨ β ⟩ _    ⟨ assoc-l-◆ ⟩-∼
                map f ◆ (⟨ α ⟩ _ ◆ ⟨ β ⟩ _)    ∎

  instance
    isCategory:Functor : isCategory (𝐅𝐮𝐧𝐜 𝒞 𝒟)
    isCategory.Hom isCategory:Functor = Natural
    isCategory.isSetoid:Hom isCategory:Functor = isSetoid:Natural
    isCategory.id isCategory:Functor           = id-𝐅𝐮𝐧𝐜
    isCategory._◆_ isCategory:Functor          = _◆-𝐅𝐮𝐧𝐜_
    isCategory.unit-l-◆ isCategory:Functor     = componentwise $ λ _ -> unit-l-◆
    isCategory.unit-r-◆ isCategory:Functor     = componentwise $ λ _ -> unit-r-◆
    isCategory.unit-2-◆ isCategory:Functor     = componentwise $ λ _ -> unit-2-◆
    isCategory.assoc-l-◆ isCategory:Functor    = componentwise $ λ _ -> assoc-l-◆
    isCategory.assoc-r-◆ isCategory:Functor    = componentwise $ λ _ -> assoc-r-◆
    isCategory._◈_ isCategory:Functor          = λ p q -> componentwise (λ x -> ⟨ p ⟩ x ◈ ⟨ q ⟩ x)

  instance
    isSetoid:Functor : isSetoid (𝐅𝐮𝐧𝐜 𝒞 𝒟)
    isSetoid:Functor = isSetoid:byCategory



