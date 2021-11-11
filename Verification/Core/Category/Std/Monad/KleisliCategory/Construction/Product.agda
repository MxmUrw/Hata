
module Verification.Core.Category.Std.Monad.KleisliCategory.Construction.Product where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Definition


open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product


module _ {𝒞 : Category 𝑖} {T : Monad 𝒞} {{_ : hasFiniteProducts 𝒞}} where

  infixl 70 _⊓-𝐊𝐥𝐬_
  _⊓-𝐊𝐥𝐬_ : (a b : Kleisli T) -> Kleisli T
  _⊓-𝐊𝐥𝐬_ a b = incl (⟨ a ⟩ ⊓ ⟨ b ⟩)



  module _ {a b : Kleisli T} where

    π₀-𝐊𝐥𝐬 : a ⊓-𝐊𝐥𝐬 b ⟶ a
    π₀-𝐊𝐥𝐬 = incl (π₀ ◆ pure)

    π₁-𝐊𝐥𝐬 : a ⊓-𝐊𝐥𝐬 b ⟶ b
    π₁-𝐊𝐥𝐬 = incl (π₁ ◆ pure)

    ⧼_⧽-𝐊𝐥𝐬 : ∀{x} -> ((x ⟶ a) × (x ⟶ b)) -> x ⟶ a ⊓-𝐊𝐥𝐬 b
    ⧼_⧽-𝐊𝐥𝐬 (f , g) = incl {!!}

    instance
      isProduct:⊓-𝐊𝐥𝐬 : isProduct a b (a ⊓-𝐊𝐥𝐬 b)
      isProduct.π₀ isProduct:⊓-𝐊𝐥𝐬             = π₀-𝐊𝐥𝐬
      isProduct.π₁ isProduct:⊓-𝐊𝐥𝐬             = π₁-𝐊𝐥𝐬
      isProduct.⧼ isProduct:⊓-𝐊𝐥𝐬 ⧽            = ⧼_⧽-𝐊𝐥𝐬
      isProduct.isSetoidHom:⧼⧽ isProduct:⊓-𝐊𝐥𝐬 = {!!}
      isProduct.reduce-π₀ isProduct:⊓-𝐊𝐥𝐬      = {!!}
      isProduct.reduce-π₁ isProduct:⊓-𝐊𝐥𝐬      = {!!}
      isProduct.expand-⊓ isProduct:⊓-𝐊𝐥𝐬       = {!!}











