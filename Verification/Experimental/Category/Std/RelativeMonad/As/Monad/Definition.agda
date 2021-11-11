
module Verification.Core.Category.Std.RelativeMonad.As.Monad.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.Monad.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {I : Functor 𝒞 𝒟} where


  record Re⁻¹ (M : RelativeMonad I) : 𝒰 ()



