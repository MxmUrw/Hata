
module Verification.Core.Data.Expr.Variant.Token.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Set.Setoid.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Theory.Std.Inference.Definition

open import Verification.Core.Data.Expr.Variant.Token.Data
open import Verification.Core.Data.Expr.Variant.Token.Definition



module _ {𝒹 : TokenExprData} where
  map-TokenExpr : ∀{A B} -> (A -> B) -> TokenExpr 𝒹 A -> TokenExpr 𝒹 B
  map-TokenExpr = {!!}

  instance
    isFunctor:TokenExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (TokenExpr 𝒹)
    isFunctor.map isFunctor:TokenExpr = map-TokenExpr
    isFunctor.isSetoidHom:map isFunctor:TokenExpr = {!!}
    isFunctor.functoriality-id isFunctor:TokenExpr = {!!}
    isFunctor.functoriality-◆ isFunctor:TokenExpr = {!!}

  instance
    isMonad:TokenExpr : isMonad (TokenExpr 𝒹)
    isMonad.pure isMonad:TokenExpr = {!!}
    isMonad.join isMonad:TokenExpr = {!!}
    isMonad.isNatural:pure isMonad:TokenExpr = {!!}
    isMonad.isNatural:join isMonad:TokenExpr = {!!}
    isMonad.unit-l-join isMonad:TokenExpr = {!!}
    isMonad.unit-r-join isMonad:TokenExpr = {!!}
    isMonad.assoc-join isMonad:TokenExpr = {!!}

TokenExprInfer : (d : TokenExprData) -> 𝐈𝐧𝐟𝐞𝐫 _
TokenExprInfer 𝒹 = incl (_ , TokenExpr 𝒹)







