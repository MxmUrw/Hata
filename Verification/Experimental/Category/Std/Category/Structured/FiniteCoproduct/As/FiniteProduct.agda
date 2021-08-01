
module Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.As.Monoid


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
  instance
    hasFiniteProducts:ᵒᵖ : hasFiniteProducts (𝒞 ᵒᵖ)
    hasFiniteProducts._⊓_ hasFiniteProducts:ᵒᵖ = _⊔_
    hasFiniteProducts.isProduct:⊓ hasFiniteProducts:ᵒᵖ = it
    hasFiniteProducts.⊤ hasFiniteProducts:ᵒᵖ = ⊥
    hasFiniteProducts.isTerminal:⊤ hasFiniteProducts:ᵒᵖ = it



