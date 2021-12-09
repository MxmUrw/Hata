
module Verification.Core.Data.Tree.Variant.Token.Instance.Monad where

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


open import Verification.Core.Data.Tree.Variant.Token.Data
open import Verification.Core.Data.Tree.Variant.Token.Definition



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

