
module Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Variant.Indexed where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
-- open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Notation.Associativity


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where

  record isIndexedCoproduct {I : 𝒰 𝑘} (aᵢ : I -> 𝒞) (x : 𝒞) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field ιᵢ : ∀ i -> aᵢ i ⟶ x
    field ⦗_⦘ᵢ : ∀{y} -> (∀ i -> aᵢ i ⟶ y) -> x ⟶ y
    field reduce-ιᵢ : ∀{y} -> (f : ∀ i -> aᵢ i ⟶ y) -> ∀ i -> ιᵢ i ◆ ⦗ f ⦘ᵢ ∼ f i
    field expand-ιᵢ : ∀{y} -> (f : x ⟶ y) -> f ∼ ⦗ (λ i -> ιᵢ i ◆ f) ⦘ᵢ

  open isIndexedCoproduct {{...}} public

record hasIndexedCoproducts {𝑗} {𝑖} (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  infixl 80 ⨆ᵢ
  field ⨆ᵢ : ∀{I : 𝒰 𝑗} -> (I -> ⟨ 𝒞 ⟩) -> ⟨ 𝒞 ⟩
  field {{isIndexedCoproduct:⨆ᵢ}} : ∀{I : 𝒰 𝑗} -> ∀{x : I -> ⟨ 𝒞 ⟩} -> isIndexedCoproduct x (⨆ᵢ x)

open hasIndexedCoproducts {{...}} public




