
module Verification.Experimental.Data.SyntaxTree.Variant.Base.Instance.Infer where

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

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.Task


open import Verification.Experimental.Data.SyntaxTree.Definition
open import Verification.Experimental.Data.SyntaxTree.Variant.Base.Definition
open import Verification.Experimental.Data.SyntaxTree.Variant.Base.Instance.Monad

open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.Expr.Variant.Base.Instance.Monad

module _ {A : 𝒰 𝑖} where
  Vec→List : Vec A n -> List A
  Vec→List [] = []
  Vec→List (x ∷ xs) = x ∷ Vec→List xs

module _ {d0 : BaseExprData} {d1 : SyntaxTreeData} (ϕ : TokenType d0 ≅ TokenType d1) where
  mutual
    printᵘ-BaseSyntaxTrees : ∀{A} -> Vec (BaseSyntaxTree d1 A) n -> Vec (BaseExpr d0 A) n
    printᵘ-BaseSyntaxTrees [] = []
    printᵘ-BaseSyntaxTrees (x ∷ xs) = (printᵘ-BaseSyntaxTree x) ∷ (printᵘ-BaseSyntaxTrees xs)

    printᵘ-BaseSyntaxTree : ∀{A} -> BaseSyntaxTree d1 A -> BaseExpr d0 A
    printᵘ-BaseSyntaxTree (hole x) = hole x
    printᵘ-BaseSyntaxTree (var x) = var x
    printᵘ-BaseSyntaxTree (node t x) = list (token (⟨ ϕ ⟩⁻¹ t) ∷ (printᵘ-BaseSyntaxTrees x))
    printᵘ-BaseSyntaxTree (annotation x e) = annotation x (printᵘ-BaseSyntaxTree e)

  mutual
    parseᵘ-BaseSyntaxTrees : ∀{A} -> Vec (BaseExpr d0 A) n -> Vec (BaseSyntaxTree d1 (BaseExpr d0 A)) n
    parseᵘ-BaseSyntaxTrees [] = []
    parseᵘ-BaseSyntaxTrees (x ∷ xs) = (parseᵘ-BaseSyntaxTree x) ∷ (parseᵘ-BaseSyntaxTrees xs)

    parseᵘ-BaseSyntaxTree : ∀{A} -> BaseExpr d0 A -> BaseSyntaxTree d1 (BaseExpr d0 A)
    parseᵘ-BaseSyntaxTree (hole x) = hole (hole x)
    parseᵘ-BaseSyntaxTree (var x) = var x
    parseᵘ-BaseSyntaxTree (token x) with TokenSize d1 (⟨ ϕ ⟩ x) ≟-Str 0
    ... | yes p = node (⟨ ϕ ⟩ x) (transport-Str (cong-Str (λ ξ -> Vec (BaseSyntaxTree d1 (BaseExpr d0 _)) ξ) (sym-≣ p)) [])
    ... | no ¬p = hole (annotation ("This token has " <> show (TokenSize d1 (⟨ ϕ ⟩ x)) <> " arguments, but has been applied to none.")
                                   (token x))
    parseᵘ-BaseSyntaxTree (list {zero} []) = hole (annotation "Empty expressions are not allowed." (list []))
    parseᵘ-BaseSyntaxTree (list {suc n} (token x ∷ xs)) with TokenSize d1 (⟨ ϕ ⟩ x) ≟-Str n
    ... | yes refl-≣ = node (⟨ ϕ ⟩ x) (parseᵘ-BaseSyntaxTrees xs)
    ... | no ¬p = hole (annotation ("This token has " <> show (TokenSize d1 (⟨ ϕ ⟩ x)) <> " arguments, but has been applied to " <> show n <> ".")
                                   ((list (token x ∷ xs))))
    parseᵘ-BaseSyntaxTree (list {suc n} (x ∷ xs)) = hole (annotation "The first element of an expression has to be a token." (list (x ∷ xs)))
    parseᵘ-BaseSyntaxTree (annotation x e) = annotation x (parseᵘ-BaseSyntaxTree e)

  print-BaseSyntaxTree : 大MonadHom (_ , BaseSyntaxTree d1) ((_ , BaseExpr d0))
  print-BaseSyntaxTree = record { fst = id ; snd = (λ _ -> printᵘ-BaseSyntaxTree) since {!!} }

  isInferHom:print-BaseSyntaxTree : isInferHom print-BaseSyntaxTree
  isInferHom:print-BaseSyntaxTree = record
    { inferF = id
    ; infer = (λ x → parseᵘ-BaseSyntaxTree) since {!!}
    ; eval-infer = (λ x → id) since {!!}
    }

  infer-BaseSyntaxTree : BaseSyntaxTreeInfer d1 ⟶ BaseExprInfer d0
  infer-BaseSyntaxTree = subcathom print-BaseSyntaxTree isInferHom:print-BaseSyntaxTree


  BaseSyntaxTreeInferenceTask : InferenceTask _
  BaseSyntaxTreeInferenceTask = inferenceTask (BaseExprInfer d0) (hasTextInfer:BaseExpr d0) (BaseSyntaxTreeInfer d1) infer-BaseSyntaxTree





