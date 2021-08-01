
module Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.Monoid where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Experimental.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct



module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is FiniteCoproductCategory 𝑖}} where

  private instance
    _ : isSetoid 𝒞
    _ = isSetoid:byCategory

  private
    𝒞ᵒᵖ : Category _
    𝒞ᵒᵖ = ′ 𝒞 ′ ᵒᵖ
    instance
      _ : isMonoid (𝒞 since isSetoid:byCategory {{of 𝒞ᵒᵖ}})
      _ = isMonoid:byHasFiniteProducts

  isMonoid:byHasFiniteCoproducts : isMonoid ′ 𝒞 ′
  isMonoid:byHasFiniteCoproducts = isMonoid:byᵒᵖ


