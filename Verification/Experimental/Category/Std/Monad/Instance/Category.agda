
module Verification.Experimental.Category.Std.Monad.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Instance.2Category
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {T : 𝒞 -> 𝒞} {{_ : Monad ′ 𝒞 ′ on T}} where
  module ShortMonadNotation where
    --------------
    -- Does not work, probably implicit argument confusion
    --
    -- ηᵘ : ∀ {a : 𝒞} -> a ⟶ T a
    -- ηᵘ = pure
    -- macro η = #structureOn (λ {a} -> ηᵘ {a})
    --
    -----

    η : Natural id ′ T ′
    η = pure since it

    μ : Natural (′ T ′ ◆-𝐂𝐚𝐭 ′ T ′) ′ T ′
    μ = join since it

open ShortMonadNotation

module _ (𝒞 : Category 𝑖) where
  macro 𝐌𝐧𝐝 = #structureOn (Monad 𝒞)

module _ {𝒞 : Category 𝑖} where

  record isMonadHom {S T : Monad 𝒞} (α : Natural ′ ⟨ S ⟩ ′ ′ ⟨ T ⟩ ′) : 𝒰 𝑖 where
    field pres-η : η ◆ α ∼ η
    field pres-μ : μ ◆ α ∼ ((α ⇃◆⇂ α) ◆ μ)

  isMonadHom:id : ∀{S : Monad 𝒞} -> isMonadHom {S} {S} id
  isMonadHom:id {S} = record { pres-η = lem-01 ; pres-μ = {!assoc-l-◆ {{of 𝒞}} ∙ ?!} }
    where
      lem-01 : (η {T = ⟨ S ⟩} ◆-𝐅𝐮𝐧𝐜 id-𝐅𝐮𝐧𝐜) ∼-Natural η
      lem-01 = unit-r-◆ {{of 𝒞}}


  private
    SubcategoryData-𝐌𝐧𝐝 : SubcategoryData (𝐅𝐮𝐧𝐜 𝒞 𝒞) (Monad 𝒞)
    SubcategoryData-𝐌𝐧𝐝 = subcatdata (λ x → ′ ⟨ x ⟩ ′) (λ {a b} -> isMonadHom {a} {b})

  isSubcategory:𝐌𝐧𝐝 : isSubcategory SubcategoryData-𝐌𝐧𝐝
  isSubcategory.closed-◆ isSubcategory:𝐌𝐧𝐝 = {!!}
  isSubcategory.closed-id isSubcategory:𝐌𝐧𝐝 = isMonadHom:id






