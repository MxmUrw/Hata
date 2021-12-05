
module Verification.Core.Data.Product.Instance.Functor where

open import Verification.Conventions
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor

open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Product.Instance.Product


instance
  isFunctor:×-𝒰 : isFunctor (𝐔𝐧𝐢𝐯 𝑖 ×-𝐂𝐚𝐭 𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) (λ₋ _×-𝒰_)
  isFunctor:×-𝒰 = isFunctor:⊓




