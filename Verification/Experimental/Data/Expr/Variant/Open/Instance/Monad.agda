
module Verification.Experimental.Data.Expr.Variant.Open.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Expr.Variant.Base.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Monad.Definition

open import Verification.Experimental.Data.Expr.Variant.Open.Definition

module _ {A : 𝒰₀} {D : TokenDefinition A} {V : 𝒰₀} {vs : 人List V} where
  instance
    isFunctor:OpenExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (OpenExpr D vs)
    isFunctor.map isFunctor:OpenExpr = {!!}
    isFunctor.isSetoidHom:map isFunctor:OpenExpr = {!!}
    isFunctor.functoriality-id isFunctor:OpenExpr = {!!}
    isFunctor.functoriality-◆ isFunctor:OpenExpr = {!!}



