
module Verification.Experimental.Data.Expr.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Subcategory.Full


data Exprᵘ (B : 𝒰 𝑖) (A : 𝐅𝐢𝐧𝐈𝐱 (⊤-𝒰 {𝑖})) : 𝒰 𝑖 where
  val : B -> Exprᵘ B A
  var : ∀{a} -> ⟨ A ⟩ ∍ a -> Exprᵘ B A
  statements : List (Exprᵘ B A) -> Exprᵘ B A


{-

-- rel monad

data Exprᵘ (B : 𝒰 𝑖) (A : 𝐅𝐢𝐧𝐈𝐱 (⊤-𝒰 {𝑖})) : 𝒰 𝑖 where
  val : B -> Exprᵘ B A
  var : ∀{a} -> ⟨ A ⟩ ∍ a -> Exprᵘ B A
  statements : List (Exprᵘ B A) -> Exprᵘ B A

module _ (B : 𝒰 𝑖) where
  Expr : 𝐅𝐢𝐧𝐈𝐱 ⊤-𝒰 -> 𝐈𝐱 (⊤-𝒰 {𝑖}) (𝐔𝐧𝐢𝐯 𝑖)
  Expr A = indexed (λ i -> Exprᵘ B A)


-}


{-
-- product theory

open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Module

module _ {A : 𝒰 𝑖} (a b : A) where
  data 𝕋List₁ : List A -> A -> 𝒰 𝑖 where
    []ᵗ : 𝕋List₁ [] a
    ∷ᵗ : 𝕋List₁ (b ∷ a ∷ []) a



module _ (B : 𝒰 𝑖) where
  data 𝕋Expr₀ : 𝒰 𝑖 where
    分ᵗ 全ᵗ : 𝕋Expr₀

  data 𝕋Expr₁ : List 𝕋Expr₀ → 𝕋Expr₀ → 𝒰 𝑖 where
    val : B -> 𝕋Expr₁ [] 全ᵗ
    list : ∀{a b} -> 𝕋List₁ 分ᵗ 全ᵗ a b -> 𝕋Expr₁ a b
    statements : 𝕋Expr₁ (分ᵗ ∷ []) 全ᵗ



  𝕋Expr : ProductTheory 𝑖
  Sort 𝕋Expr = 𝕋Expr₀
  isDiscrete:Sort 𝕋Expr = {!!}
  isSet-Str:Sort 𝕋Expr = {!!}
  Con 𝕋Expr = 𝕋Expr₁
  isDiscrete:Con 𝕋Expr = {!!}


-}



