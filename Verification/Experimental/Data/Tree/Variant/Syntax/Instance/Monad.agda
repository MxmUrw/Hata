
module Verification.Experimental.Data.Tree.Variant.Syntax.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Nat.Definition
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
open import Verification.Experimental.Data.Indexed.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Theory.Std.Inference.Definition


open import Verification.Experimental.Data.Tree.Variant.Syntax.Data
open import Verification.Experimental.Data.Tree.Variant.Syntax.Definition



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

