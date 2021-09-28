
module Verification.Experimental.Data.Product.Instance.Functor where

open import Verification.Conventions
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor

open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Product.Instance.Product


instance
  isFunctor:×-𝒰 : isFunctor (𝐔𝐧𝐢𝐯 𝑖 ×-𝐂𝐚𝐭 𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) (λ₋ _×-𝒰_)
  isFunctor:×-𝒰 = isFunctor:⊓




