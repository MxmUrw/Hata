
module Verification.Experimental.Data.Tree.Variant.Syntax.Instance.Infer where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.AllOf.Product
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.AllOf.List
open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Constant
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Set.Setoid.As.Category
open import Verification.Experimental.Set.Setoid.Discrete
open import Verification.Experimental.Set.Setoid.Definition

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Duplicate

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.Task

open import Verification.Experimental.Data.Tree.Variant.Syntax.Data
open import Verification.Experimental.Data.Tree.Variant.Syntax.Definition
open import Verification.Experimental.Data.Tree.Variant.Syntax.Instance.Monad

open import Verification.Experimental.Data.Tree.Variant.Token.Data
open import Verification.Experimental.Data.Tree.Variant.Token.Definition
open import Verification.Experimental.Data.Tree.Variant.Token.Instance.Monad


data SyntaxTreeToken : 𝒰₀ where
  binder : SyntaxTreeToken

tokenSize-SyntaxTreeToken : SyntaxTreeToken -> ℕ
tokenSize-SyntaxTreeToken binder = 2

tokenName-SyntaxTreeToken : SyntaxTreeToken -> Text
tokenName-SyntaxTreeToken binder = "↦"

toTokenTreeData : SyntaxTreeData -> TokenTreeData
toTokenTreeData 𝒹 = record
  { TokenType = SyntaxTreeToken + (TokenType 𝒹)
  ; tokenSize = either tokenSize-SyntaxTreeToken (tokenSize 𝒹)
  ; tokenName = either tokenName-SyntaxTreeToken (tokenName 𝒹)
  ; tokenList = left binder ∷ map-List right (tokenList 𝒹) 
  }

private δ = toTokenTreeData

module _ {𝒹 : SyntaxTreeData} where
  -- mutual
  --   printᵘ-SyntaxTrees : ∀{A} -> Vec (SyntaxTree 𝒹 A) n -> Vec (TokenTree (δ 𝒹) A) n
  --   printᵘ-SyntaxTrees = ?
  --   -- printᵘ-SyntaxTrees [] = []
  --   -- printᵘ-SyntaxTrees (x ∷ xs) = (printᵘ-SyntaxTree x) ∷ (printᵘ-SyntaxTrees xs)

  --   printᵘ-SyntaxTree : ∀{A} -> SyntaxTree 𝒹 A -> TokenTree (δ 𝒹) A
  --   printᵘ-SyntaxTree = ?
    -- printᵘ-SyntaxTree (hole x) = hole x
    -- printᵘ-SyntaxTree (var x) = var x
    -- printᵘ-SyntaxTree (node t x) = list (token t ∷ (printᵘ-SyntaxTrees x))
    -- printᵘ-SyntaxTree (annotation x e) = annotation x (printᵘ-SyntaxTree e)

  print-SyntaxTree : 大MonadHom (_ , SyntaxTree 𝒹) (_ , TokenTree (δ 𝒹))
  print-SyntaxTree = record { fst = {!⨆ᶠ!} ; snd = {!!} }


  infer-SyntaxTree : SyntaxTreeInfer 𝒹 ⟶ TokenTreeInfer (δ 𝒹)
  infer-SyntaxTree = subcathom print-SyntaxTree {!!}



