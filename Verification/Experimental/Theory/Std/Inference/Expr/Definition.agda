
module Verification.Experimental.Theory.Std.Inference.Expr.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition


data Exprᵘ (B : 𝒰 𝑖) (A : 𝐅𝐢𝐧𝐈𝐱 (⊤-𝒰 {𝑖})) : 𝒰 𝑖 where


module _ (B : 𝒰 𝑖) where
  Expr : 𝐅𝐢𝐧𝐈𝐱 ⊤-𝒰 -> 𝐈𝐱 (⊤-𝒰 {𝑖}) (𝐔𝐧𝐢𝐯 𝑖)
  Expr A = indexed (λ i -> Exprᵘ B A)





