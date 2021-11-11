
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Instance.SmallCategories where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Iso
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Lift

------------------
-- ===* Category with 2 points

data 𝟚-𝒰 : 𝒰₀ where
  ₀ ₁ : 𝟚-𝒰

Category:𝟚 = Category:Discrete 𝟚-𝒰
instance ICategory:𝟚 = #openstruct Category:𝟚

instance
  Notation-𝟚:Category : ∀{𝑖} -> Notation-𝟚 (Category 𝑖)
  Notation-𝟚.`𝟚` (Notation-𝟚:Category {𝑖}) = ↑ Category:𝟚


------------------
-- ===* Category with pair of arrows

data Pair : 𝒰₀ where
  ₀ ₁ : Pair

data PairHom : Pair -> Pair -> 𝒰₀ where
  arr₀ : PairHom ₀ ₁
  arr₁ : PairHom ₀ ₁

Quiver:Pair : Quiver (many ℓ₀)
⟨ Quiver:Pair ⟩ = Pair
IQuiver.Edge (of Quiver:Pair) = PairHom
IQuiver._≈_ (of Quiver:Pair) = _≡_
IQuiver.isEquivRelInst (of Quiver:Pair) = isEquivRel:Path

Category:Pair = Category:Free (Quiver:Pair)

instance
  ICategory:Pair = of Category:Pair

𝔼 : ∀{𝑖} -> Category 𝑖
𝔼 = ↑ Category:Pair



