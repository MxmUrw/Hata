
module Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Monad where

open import Verification.Conventions hiding (ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
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

open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Definition



module _ {𝒹 : ATokenExprData} {Ann} where
  map-ATokenExpr : ∀{A B} -> (A -> B) -> ATokenExpr 𝒹 Ann A -> ATokenExpr 𝒹 Ann B
  map-ATokenExpr = {!!}

  instance
    isFunctor:ATokenExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (ATokenExpr 𝒹 Ann)
    isFunctor.map isFunctor:ATokenExpr = map-ATokenExpr
    isFunctor.isSetoidHom:map isFunctor:ATokenExpr = {!!}
    isFunctor.functoriality-id isFunctor:ATokenExpr = {!!}
    isFunctor.functoriality-◆ isFunctor:ATokenExpr = {!!}

  instance
    isMonad:ATokenExpr : isMonad (ATokenExpr 𝒹 Ann)
    isMonad.pure isMonad:ATokenExpr = {!!}
    isMonad.join isMonad:ATokenExpr = {!!}
    isMonad.isNatural:pure isMonad:ATokenExpr = {!!}
    isMonad.isNatural:join isMonad:ATokenExpr = {!!}
    isMonad.unit-l-join isMonad:ATokenExpr = {!!}
    isMonad.unit-r-join isMonad:ATokenExpr = {!!}
    isMonad.assoc-join isMonad:ATokenExpr = {!!}

ATokenExprInfer : (d : ATokenExprData) -> (Ann : _) -> 𝐈𝐧𝐟𝐞𝐫 _
ATokenExprInfer 𝒹 Ann = incl (_ , ATokenExpr 𝒹 Ann)





