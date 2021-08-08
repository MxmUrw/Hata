
module Verification.Experimental.Category.Std.Morphism.Mono.Subcategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.Mono.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso


module _ (𝒞 : Category 𝑖) where
  record Subₘₒₙₒ : 𝒰 (𝑖 ⌄ 0) where
    constructor incl
    field ⟨_⟩ : ⟨ 𝒞 ⟩

  open Subₘₒₙₒ public

  macro 𝐒𝐮𝐛ₘₒₙₒ = #structureOn Subₘₒₙₒ

module _ {𝒞 : Category 𝑖} where
  private
    subₘₒₙₒ : SubcategoryData 𝒞 (Subₘₒₙₒ 𝒞)
    subₘₒₙₒ = subcatdata ⟨_⟩ isMono

    lem-1 : ∀{a : ⟨ 𝒞 ⟩} -> isMono (id {a = a})
    lem-1 = mono (λ p → unit-r-◆ ⁻¹ ∙ p ∙ unit-r-◆)

    lem-2 : ∀{a b c : ⟨ 𝒞 ⟩} -> {f : a ⟶ b} -> {g : b ⟶ c}
            -> isMono f -> isMono g -> isMono (f ◆ g)
    lem-2 {a} {b} {c} {f} {g} fp gp = mono P
      where
        P : ∀{x : ⟨ 𝒞 ⟩} {α β : x ⟶ a} -> (α ◆ (f ◆ g)) ∼ (β ◆ (f ◆ g)) -> α ∼ β
        P {α = α} {β} p =
          let q : (α ◆ f) ◆ g ∼ (β ◆ f) ◆ g
              q = assoc-l-◆ ∙ p ∙ assoc-r-◆
              Q : α ◆ f ∼ β ◆ f
              Q = cancel-mono {{_}} {{gp}} q
          in cancel-mono {{_}} {{fp}} Q

  instance
    isSubcategory:subₘₒₙₒ : isSubcategory (subₘₒₙₒ)
    isSubcategory:subₘₒₙₒ =
      record
      { closed-◆  = lem-2
      ; closed-id = lem-1
      }

  instance
    isCategory:Subₘₒₙₒ : isCategory (𝐒𝐮𝐛ₘₒₙₒ 𝒞)
    isCategory:Subₘₒₙₒ = isCategory:bySubcategory

  instance
    isSetoid:𝐒𝐮𝐛ₘₒₙₒ : isSetoid (𝐒𝐮𝐛ₘₒₙₒ 𝒞)
    isSetoid:𝐒𝐮𝐛ₘₒₙₒ = isSetoid:byCategory


