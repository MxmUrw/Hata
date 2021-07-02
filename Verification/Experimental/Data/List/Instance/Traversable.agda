
module Verification.Experimental.Data.List.Instance.Traversable where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category

open import Verification.Experimental.Category.Std.Monad.Definition

open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation


instance
  isTraversable:List : isTraversable (List {𝑖})
  isTraversable:List {𝑖} = traversable (λ {M} {{MM}} {A} xs -> f {M} {MM} {A} xs)
    where
      module _ {M : 𝒰' 𝑖 → 𝒰' 𝑖} { MM : Monad ′ 𝒰' 𝑖 ′ on M } where
          f : {A : 𝒰' 𝑖} → List (M A) → M (List A)
          f [] = return []
          f (x ∷ xs) = do
            x <- x
            xs <- f xs
            return (x ∷ xs)



