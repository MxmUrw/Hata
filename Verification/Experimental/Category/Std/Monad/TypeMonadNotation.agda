
module Verification.Experimental.Category.Std.Monad.TypeMonadNotation where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category

open import Verification.Experimental.Category.Std.Monad.Definition

open import Verification.Experimental.Data.Universe.Everything


module _ {T : _ -> _} {{_ : Monad (𝐓𝐲𝐩𝐞 𝑖) on T}} where
  _>>=_ : ∀{A B : 𝒰 𝑖} -> (T A) -> (A -> T B) -> T B
  a >>= f =
    let x = ⟨ map (incl f) ⟩ a
    in ⟨ join ⟩ x

  _>>_ : ∀{A B : 𝒰 𝑖} -> (T A) -> T B -> T B
  a >> b = a >>= const b

  return : {A : 𝒰 𝑖} -> A -> T A
  return = ⟨ pure ⟩



