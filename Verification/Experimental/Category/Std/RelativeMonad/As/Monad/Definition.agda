
module Verification.Experimental.Category.Std.RelativeMonad.As.Monad.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.Monad.Definition


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {I : Functor 𝒞 𝒟} where


  record Re⁻¹ (M : RelativeMonad I) : 𝒰 ()



