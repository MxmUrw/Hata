
module Verification.Experimental.Data.Product.Instance.Product where

open import Verification.Conventions
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor

open import Verification.Experimental.Data.Product.Definition

module _ {A B : 𝒰 𝑖} where
  instance
    isProduct:× : isProduct A B (A × B)
    isProduct.π₀ isProduct:× = fst
    isProduct.π₁ isProduct:× = snd
    isProduct.⧼ isProduct:× ⧽ = λ (f , g) x -> (f x , g x)
    isProduct.isSetoidHom:⧼⧽ isProduct:× = record { cong-∼ = λ (p , q) → λ i x → p i x , q i x }
    isProduct.reduce-π₀ isProduct:× = refl
    isProduct.reduce-π₁ isProduct:× = refl
    isProduct.expand-⊓ isProduct:× = refl

instance
  isTerminal:⊤-𝒰 : isTerminal (⊤-𝒰 {𝑖})
  isTerminal:⊤-𝒰 = record { intro-⊤ = const tt ; expand-⊤ = funExt lem-1 }
    where
      lem-1 : ∀{A} {f : A -> ⊤-𝒰} -> ∀ a -> (f a ≡ tt)
      lem-1 {f = f} a with f a
      ... | tt = refl-≡

  hasTerminal:𝐔𝐧𝐢𝐯 : hasTerminal (𝐔𝐧𝐢𝐯 𝑖)
  hasTerminal:𝐔𝐧𝐢𝐯 = record { ⊤ = ⊤-𝒰 }

  hasProducts:𝐔𝐧𝐢𝐯 : hasProducts (𝐔𝐧𝐢𝐯 𝑖)
  hasProducts:𝐔𝐧𝐢𝐯 = record { _⊓_ = _×-𝒰_ }

  hasFiniteProducts:𝐔𝐧𝐢𝐯 : hasFiniteProducts (𝐔𝐧𝐢𝐯 𝑖)
  hasFiniteProducts:𝐔𝐧𝐢𝐯 = hasFiniteProducts:default



