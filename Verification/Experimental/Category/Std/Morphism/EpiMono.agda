
module Verification.Experimental.Category.Std.Morphism.EpiMono where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record isMono {a b : 𝒞} (ϕ : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor mono
    field cancel-mono : ∀{x : 𝒞} -> ∀{α β : x ⟶ a} -> α ◆ ϕ ∼ β ◆ ϕ -> α ∼ β

  open isMono {{...}} public

module _ (𝒞 : Category 𝑖) where
  record Sub-mono : 𝒰 (𝑖 ⌄ 0) where
    constructor incl
    field ⟨_⟩ : ⟨ 𝒞 ⟩

  open Sub-mono public

  macro 𝐒𝐮𝐛-mono = #structureOn Sub-mono

module _ {𝒞 : Category 𝑖} where
  private
    sub-mono : SubcategoryData 𝒞 (Sub-mono 𝒞)
    sub-mono = subcatdata ⟨_⟩ isMono

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
    isSubcategory:sub-mono : isSubcategory (sub-mono)
    isSubcategory:sub-mono =
      record
      { closed-◆  = lem-2
      ; closed-id = lem-1
      }

  instance
    isCategory:Sub-mono : isCategory (𝐒𝐮𝐛-mono 𝒞)
    isCategory:Sub-mono = isCategory:bySubcategory


