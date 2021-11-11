
module Verification.Experimental.Data.Expr.Variant.List.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.AllOf.Product
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Constant
open import Verification.Experimental.Set.Setoid.As.Category
open import Verification.Experimental.Set.Setoid.Discrete
open import Verification.Experimental.Set.Setoid.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Theory.Std.Inference.Definition

-- open import Verification.Experimental.Data.Expr.Variant.List.Data
open import Verification.Experimental.Data.Expr.Variant.List.Definition



map-ListExpr : ∀{A B} -> (A -> B) -> ListExpr A -> ListExpr B
map-ListExpr = {!!}

instance
  isFunctor:ListExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (ListExpr)
  isFunctor.map isFunctor:ListExpr = map-ListExpr
  isFunctor.isSetoidHom:map isFunctor:ListExpr = {!!}
  isFunctor.functoriality-id isFunctor:ListExpr = {!!}
  isFunctor.functoriality-◆ isFunctor:ListExpr = {!!}

instance
  isMonad:ListExpr : isMonad (ListExpr)
  isMonad.pure isMonad:ListExpr = {!!}
  isMonad.join isMonad:ListExpr = {!!}
  isMonad.isNatural:pure isMonad:ListExpr = {!!}
  isMonad.isNatural:join isMonad:ListExpr = {!!}
  isMonad.unit-l-join isMonad:ListExpr = {!!}
  isMonad.unit-r-join isMonad:ListExpr = {!!}
  isMonad.assoc-join isMonad:ListExpr = {!!}

ListExprInfer : 𝐈𝐧𝐟𝐞𝐫 _
ListExprInfer = incl (_ , ListExpr)



