
module Verification.Experimental.Data.SyntaxTree.Variant.Base.Instance.Monad where

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


open import Verification.Experimental.Data.SyntaxTree.Definition
open import Verification.Experimental.Data.SyntaxTree.Variant.Base.Definition



module _ {d : SyntaxTreeData} where
  map-BaseSyntaxTree : ∀{A B} -> (A -> B) -> BaseSyntaxTree d A -> BaseSyntaxTree d B
  map-BaseSyntaxTree = {!!}

  instance
    isFunctor:BaseSyntaxTree : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (BaseSyntaxTree d)
    isFunctor.map isFunctor:BaseSyntaxTree = map-BaseSyntaxTree
    isFunctor.isSetoidHom:map isFunctor:BaseSyntaxTree = {!!}
    isFunctor.functoriality-id isFunctor:BaseSyntaxTree = {!!}
    isFunctor.functoriality-◆ isFunctor:BaseSyntaxTree = {!!}

  instance
    isMonad:BaseSyntaxTree : isMonad (BaseSyntaxTree d)
    isMonad.pure isMonad:BaseSyntaxTree = {!!}
    isMonad.join isMonad:BaseSyntaxTree = {!!}
    isMonad.isNatural:pure isMonad:BaseSyntaxTree = {!!}
    isMonad.isNatural:join isMonad:BaseSyntaxTree = {!!}
    isMonad.unit-l-join isMonad:BaseSyntaxTree = {!!}
    isMonad.unit-r-join isMonad:BaseSyntaxTree = {!!}
    isMonad.assoc-join isMonad:BaseSyntaxTree = {!!}

BaseSyntaxTreeInfer : (d : SyntaxTreeData) -> 𝐈𝐧𝐟𝐞𝐫 _
BaseSyntaxTreeInfer d = incl (_ , BaseSyntaxTree d)

