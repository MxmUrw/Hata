
module Verification.Experimental.Data.Tree.Variant.Token.Instance.Monad where

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


open import Verification.Experimental.Data.Tree.Variant.Token.Data
open import Verification.Experimental.Data.Tree.Variant.Token.Definition



module _ {𝒹 : TokenTreeData} where
  map-TokenTree : ∀{A B} -> (A -> B) -> TokenTree 𝒹 A -> TokenTree 𝒹 B
  map-TokenTree = {!!}

  instance
    isFunctor:TokenTree : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (TokenTree 𝒹)
    isFunctor.map isFunctor:TokenTree = map-TokenTree
    isFunctor.isSetoidHom:map isFunctor:TokenTree = {!!}
    isFunctor.functoriality-id isFunctor:TokenTree = {!!}
    isFunctor.functoriality-◆ isFunctor:TokenTree = {!!}

  instance
    isMonad:TokenTree : isMonad (TokenTree 𝒹)
    isMonad.pure isMonad:TokenTree = {!!}
    isMonad.join isMonad:TokenTree = {!!}
    isMonad.isNatural:pure isMonad:TokenTree = {!!}
    isMonad.isNatural:join isMonad:TokenTree = {!!}
    isMonad.unit-l-join isMonad:TokenTree = {!!}
    isMonad.unit-r-join isMonad:TokenTree = {!!}
    isMonad.assoc-join isMonad:TokenTree = {!!}

TokenTreeInfer : (d : TokenTreeData) -> 𝐈𝐧𝐟𝐞𝐫 _
TokenTreeInfer 𝒹 = incl (_ , TokenTree 𝒹)

