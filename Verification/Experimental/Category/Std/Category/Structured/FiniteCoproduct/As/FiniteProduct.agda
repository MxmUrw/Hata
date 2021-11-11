
module Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Product
open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
-- open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid


module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where
  instance
    hasProducts:ᵒᵖ : hasProducts (𝒞 ᵒᵖ)
    hasProducts._⊓_ hasProducts:ᵒᵖ = _⊔_
    hasProducts.isProduct:⊓ hasProducts:ᵒᵖ = it

    hasTerminal:ᵒᵖ : hasTerminal (𝒞 ᵒᵖ)
    hasTerminal.⊤ hasTerminal:ᵒᵖ = ⊥
    hasTerminal.isTerminal:⊤ hasTerminal:ᵒᵖ = it
  instance
    hasFiniteProducts:ᵒᵖ : hasFiniteProducts (𝒞 ᵒᵖ)
    hasFiniteProducts.hasTerminal:this hasFiniteProducts:ᵒᵖ = hasTerminal:ᵒᵖ
    hasFiniteProducts.hasProducts:this hasFiniteProducts:ᵒᵖ = hasProducts:ᵒᵖ
    -- hasFiniteProducts._⊓_ hasFiniteProducts:ᵒᵖ = _⊔_
    -- hasFiniteProducts.isProduct:⊓ hasFiniteProducts:ᵒᵖ = it
    -- hasFiniteProducts.⊤ hasFiniteProducts:ᵒᵖ = ⊥
    -- hasFiniteProducts.isTerminal:⊤ hasFiniteProducts:ᵒᵖ = it



