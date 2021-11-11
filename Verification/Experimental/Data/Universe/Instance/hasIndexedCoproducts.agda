
module Verification.Experimental.Data.Universe.Instance.hasIndexedCoproducts where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
-- open import Verification.Experimental.Category.Std.Natural.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.As.Monoid
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct


module _ {I : 𝒰 𝑘} {x : I -> 𝒰 𝑘} where

  instance
    isIndexedCoproduct:∑ : isIndexedCoproduct x (∑ x)
    isIndexedCoproduct:∑ = record
      { ιᵢ = λ i x → i , x
      ; ⦗_⦘ᵢ = λ f (i , x) → f i x
      ; reduce-ιᵢ = λ f i → refl-≡
      ; expand-ιᵢ = λ f → refl-≡
      }

instance
  hasIndexedCoproducts:𝐔𝐧𝐢𝐯 : hasIndexedCoproducts (𝐔𝐧𝐢𝐯 𝑖)
  hasIndexedCoproducts:𝐔𝐧𝐢𝐯 = record { ⨆ᵢ = ∑_ }


