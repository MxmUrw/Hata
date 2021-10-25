
module Verification.Experimental.Category.Std.Monad.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Instance.2Category
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  module ShortMonadNotation where
    --------------
    -- Does not work, probably implicit argument confusion
    --
    -- ηᵘ : ∀ {a : 𝒞} -> a ⟶ T a
    -- ηᵘ = pure
    -- macro η = #structureOn (λ {a} -> ηᵘ {a})
    --
    -----
    module _ {T : 𝒞 -> 𝒞} {{_ : Monad ′ 𝒞 ′ on T}} where
      η : Natural id ′ T ′
      η = pure since it

      μ : Natural (′ T ′ ◆-𝐂𝐚𝐭 ′ T ′) ′ T ′
      μ = join since it

    module _ (T : Monad ′ 𝒞 ′) where
      ηOf : Natural id ′ ⟨ T ⟩ ′
      ηOf = pure since it

      μOf : Natural (′ ⟨ T ⟩ ′ ◆-𝐂𝐚𝐭 ′ ⟨ T ⟩ ′) ′ ⟨ T ⟩ ′
      μOf = join since it


open ShortMonadNotation

module _ (𝒞 : Category 𝑖) where
  macro 𝐌𝐧𝐝 = #structureOn (Monad 𝒞)

module _ {𝒞 : Category 𝑖} where

  record isMonadHom {S T : Monad 𝒞} (α : Natural ′ ⟨ S ⟩ ′ ′ ⟨ T ⟩ ′) : 𝒰 𝑖 where
    field pres-η : η ◆ α ∼ η
    field pres-μ : μ ◆ α ∼ ((α ⇃◆⇂ α) ◆ μ)

  open isMonadHom {{...}} public

  isMonadHom:id : ∀{S : Monad 𝒞} -> isMonadHom {S} {S} id
  isMonadHom:id {S} = record { pres-η = lem-01 ; pres-μ = {!!}} -- lem-02}
    where
      lem-01 : (ηOf S ◆-𝐅𝐮𝐧𝐜 id-𝐅𝐮𝐧𝐜) ∼-Natural η
      lem-01 = componentwise $ λ x -> unit-r-◆

      lem-02 : (μOf S ◆-𝐅𝐮𝐧𝐜 id-𝐅𝐮𝐧𝐜) ∼-Natural ((id-𝐅𝐮𝐧𝐜 {F = ′ ⟨ S ⟩ ′} ⇃◆⇂ id-𝐅𝐮𝐧𝐜 {F = ′ ⟨ S ⟩ ′}) ◆-𝐅𝐮𝐧𝐜 μ {T = ⟨ S ⟩})
      lem-02 = {!!}
               -- _ = join ◆ id            ⟨ unit-r-◆ ⟩-∼
               --   join                 ⟨ unit-l-◆ ⁻¹ ⟩-∼
               --   id ◆ join            ⟨ functoriality-id ⁻¹ ◈ refl ⟩-∼
               --   (map id) ◆ join      ⟨ unit-l-◆ ⁻¹ ◈ refl ⟩-∼
               --   (id ◆ map id) ◆ join ∎

  isMonadHom:◆ : ∀{S T U : Monad 𝒞} -> ∀{α β}
                 -> isMonadHom {S} {T} α -> isMonadHom {T} {U} β -> isMonadHom {S} {U} (α ◆ β)
  isMonadHom:◆ {S} {T} {U} {α} {β} αp βp = record { pres-η = lem-01 ; pres-μ = lem-02 }
    where
      lem-01 : (ηOf S ◆-𝐅𝐮𝐧𝐜 (α ◆-𝐅𝐮𝐧𝐜 β)) ∼ ηOf U
      lem-01 = componentwise $ λ x ->
                 (⟨ ηOf S ⟩ x ◆ (⟨ α ⟩ x ◆ ⟨ β ⟩ x))  ⟨ assoc-r-◆ ⟩-∼
                 ((⟨ ηOf S ⟩ x ◆ ⟨ α ⟩ x) ◆ ⟨ β ⟩ x)   ⟨ ⟨ pres-η {{αp}} ⟩ x ◈ refl ⟩-∼
                 (⟨ ηOf T ⟩ x ◆ ⟨ β ⟩ x)               ⟨ ⟨ pres-η {{βp}} ⟩ x ⟩-∼
                 ⟨ ηOf U ⟩  x                            ∎

      lem-02 : (μOf S ◆-𝐅𝐮𝐧𝐜 (α ◆-𝐅𝐮𝐧𝐜 β)) ∼ (((α ◆-𝐅𝐮𝐧𝐜 β) ⇃◆⇂ (α ◆-𝐅𝐮𝐧𝐜 β)) ◆-𝐅𝐮𝐧𝐜 μ)
      lem-02 = componentwise $ λ x ->
                 ⟨ μOf S ⟩ x ◆ (⟨ α ⟩ x ◆ ⟨ β ⟩ x)               ⟨ assoc-r-◆ ⟩-∼
                 (⟨ μOf S ⟩ x ◆ ⟨ α ⟩ x) ◆ ⟨ β ⟩ x               ⟨ ⟨ pres-μ {{αp}} ⟩ x ◈ refl ⟩-∼
                 (⟨ α ⇃◆⇂ α ⟩ x) ◆ ⟨ μOf T ⟩ x ◆ ⟨ β ⟩ x         ⟨ assoc-l-◆ ⟩-∼
                 (⟨ α ⇃◆⇂ α ⟩ x) ◆ (⟨ μOf T ⟩ x ◆ ⟨ β ⟩ x)       ⟨ refl ◈ ⟨ pres-μ {{βp}} ⟩ x ⟩-∼
                 (⟨ α ⇃◆⇂ α ⟩ x) ◆ (⟨ β ⇃◆⇂ β ⟩ x ◆ ⟨ μOf U ⟩ x) ⟨ assoc-r-◆ ⟩-∼
                 ((⟨ α ⇃◆⇂ α ⟩ x) ◆ ⟨ β ⇃◆⇂ β ⟩ x) ◆ ⟨ μOf U ⟩ x ⟨ ⟨ interchange-⇃◆⇂ α β α β ⟩ x ⁻¹ ◈ refl ⟩-∼

                 ⟨ (((α ◆-𝐅𝐮𝐧𝐜 β) ⇃◆⇂ (α ◆-𝐅𝐮𝐧𝐜 β)) ◆-𝐅𝐮𝐧𝐜 μ) ⟩ x ∎


  private
    SubcategoryData-𝐌𝐧𝐝 : SubcategoryData (𝐅𝐮𝐧𝐜 𝒞 𝒞) (Monad 𝒞)
    SubcategoryData-𝐌𝐧𝐝 = subcatdata (λ x → ′ ⟨ x ⟩ ′) (λ {a b} -> isMonadHom {a} {b})

  instance
    isSubcategory:𝐌𝐧𝐝 : isSubcategory SubcategoryData-𝐌𝐧𝐝
    isSubcategory.closed-◆ isSubcategory:𝐌𝐧𝐝 = isMonadHom:◆
    isSubcategory.closed-id isSubcategory:𝐌𝐧𝐝 = isMonadHom:id

  instance
    isCategory:𝐌𝐧𝐝 : isCategory (𝐌𝐧𝐝 𝒞)
    isCategory:𝐌𝐧𝐝 = isCategory:bySubcategory






