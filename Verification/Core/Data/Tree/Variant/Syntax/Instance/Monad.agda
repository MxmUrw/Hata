
module Verification.Core.Data.Tree.Variant.Syntax.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.Nat
open import Verification.Core.Data.AllOf.Universe
open import Verification.Core.Data.Expr.Variant.Base.Definition
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
open import Verification.Core.Data.Indexed.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Theory.Std.Inference.Definition


open import Verification.Core.Data.Tree.Variant.Syntax.Data
open import Verification.Core.Data.Tree.Variant.Syntax.Definition



module _ {𝒹 : SyntaxTreeData} where
  map-SyntaxTree : ∀{A B : 𝐈𝐱 _ 𝐔𝐧𝐢𝐯₀} -> (A ⟶ B) -> SyntaxTree 𝒹 A ⟶ SyntaxTree 𝒹 B
  map-SyntaxTree = {!!}

  instance
    isFunctor:SyntaxTree : isFunctor (𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)) (𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)) (SyntaxTree 𝒹)
    isFunctor.map isFunctor:SyntaxTree = map-SyntaxTree
    isFunctor.isSetoidHom:map isFunctor:SyntaxTree = {!!}
    isFunctor.functoriality-id isFunctor:SyntaxTree = {!!}
    isFunctor.functoriality-◆ isFunctor:SyntaxTree = {!!}

  instance
    isMonad:SyntaxTree : isMonad (SyntaxTree 𝒹)
    isMonad.pure isMonad:SyntaxTree = {!!}
    isMonad.join isMonad:SyntaxTree = {!!}
    isMonad.isNatural:pure isMonad:SyntaxTree = {!!}
    isMonad.isNatural:join isMonad:SyntaxTree = {!!}
    isMonad.unit-l-join isMonad:SyntaxTree = {!!}
    isMonad.unit-r-join isMonad:SyntaxTree = {!!}
    isMonad.assoc-join isMonad:SyntaxTree = {!!}

SyntaxTreeInfer : (d : SyntaxTreeData) -> 𝐈𝐧𝐟𝐞𝐫 _
SyntaxTreeInfer 𝒹 = incl (_ , SyntaxTree 𝒹)

