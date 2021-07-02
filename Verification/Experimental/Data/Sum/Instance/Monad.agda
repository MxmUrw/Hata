
module Verification.Experimental.Data.Sum.Instance.Monad where

open import Verification.Conventions
open import Verification.Experimental.Set.Function.Injective
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Sum.Instance.Functor



module _ {A : 𝒰 𝑖} where
  instance
    isMonad:+⧿ : isMonad {𝒞 = 𝐓𝐲𝐩𝐞 𝑖} (A +⧿)
    isMonad:+⧿ = monad pure-+ join-+ {{{!!}}} {{{!!}}} {!!} {!!} {!!}

      where
        pure-+ : ∀{B} -> (B ⟶ A + B)
        pure-+ = incl right

        join-+ : ∀{B : 𝒰 𝑖} -> (A +-𝒰 (A + B)) ⟶ (A + B)
        join-+ = incl (either left idf)




