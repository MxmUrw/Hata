
module Verification.Experimental.Data.Tree.Variant.Token.Instance.Infer where

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

open import Verification.Experimental.Data.Expr.Variant.Token.Data
open import Verification.Experimental.Data.Expr.Variant.Token.Definition
open import Verification.Experimental.Data.Expr.Variant.Token.Instance.Monad

open import Verification.Experimental.Data.Tree.Variant.Token.Data
open import Verification.Experimental.Data.Tree.Variant.Token.Definition
open import Verification.Experimental.Data.Tree.Variant.Token.Instance.Monad

-- open import Verification.Experimental.Data.SourceCode.Variant.Tokenized.Definition
-- open import Verification.Experimental.Data.Expr.Variant.Base.Definition
-- open import Verification.Experimental.Data.Expr.Variant.Base.Instance.Monad

-- module _ {A : 𝒰 𝑖} where
--   Vec→List : Vec A n -> List A
--   Vec→List [] = []
--   Vec→List (x ∷ xs) = x ∷ Vec→List xs


toTokenExprData : TokenTreeData -> TokenExprData
toTokenExprData 𝒹 = record { TokenType = TokenType 𝒹 ; tokenName = tokenName 𝒹 ; tokenList = tokenList 𝒹 }

private
  δ = toTokenExprData


module _ {𝒹 : TokenTreeData} where
  mutual
    printᵘ-TokenTrees : ∀{A} -> Vec (TokenTree 𝒹 A) n -> Vec (TokenExpr (δ 𝒹) A) n
    printᵘ-TokenTrees [] = []
    printᵘ-TokenTrees (x ∷ xs) = (printᵘ-TokenTree x) ∷ (printᵘ-TokenTrees xs)

    printᵘ-TokenTree : ∀{A} -> TokenTree 𝒹 A -> TokenExpr (δ 𝒹) A
    printᵘ-TokenTree (hole x) = hole x
    printᵘ-TokenTree (var x) = var x
    printᵘ-TokenTree (node t x) = list (token t ∷ (printᵘ-TokenTrees x))
    printᵘ-TokenTree (annotation x e) = annotation x (printᵘ-TokenTree e)


  mutual
    parseᵘ-TokenTrees : ∀{A} -> Vec (TokenExpr (δ 𝒹) A) n -> Vec (TokenTree 𝒹 (TokenExpr (δ 𝒹) A)) n
    parseᵘ-TokenTrees [] = []
    parseᵘ-TokenTrees (x ∷ xs) = (parseᵘ-TokenTree x) ∷ (parseᵘ-TokenTrees xs)

    parseᵘ-TokenTree : ∀{A} -> TokenExpr (δ 𝒹) A -> TokenTree 𝒹 (TokenExpr (δ 𝒹) A)
    parseᵘ-TokenTree (hole x) = hole (hole x)
    parseᵘ-TokenTree (var x) = var x
    parseᵘ-TokenTree (token x) with tokenSize 𝒹 x ≟-Str 0
    ... | yes p = node (x) (transport-Str (cong-Str (λ ξ -> Vec (TokenTree 𝒹 (TokenExpr (δ 𝒹) _)) ξ) (sym-≣ p)) [])
    ... | no ¬p = hole (annotation ("This token has " <> show (tokenSize 𝒹 (x)) <> " arguments, but has been applied to none.")
                                   (token x))
    parseᵘ-TokenTree (list {zero} []) = hole (annotation "Empty expressions are not allowed." (list []))
    parseᵘ-TokenTree (list {suc n} (token x ∷ xs)) with tokenSize 𝒹 (x) ≟-Str n
    ... | yes refl-≣ = node (x) (parseᵘ-TokenTrees xs)
    ... | no ¬p = hole (annotation ("This token has " <> show (tokenSize 𝒹 (x)) <> " arguments, but has been applied to " <> show n <> ".")
                                   ((list (token x ∷ xs))))
    parseᵘ-TokenTree (list {suc n} (x ∷ xs)) = hole (annotation "The first element of an expression has to be a token." (list (x ∷ xs)))
    parseᵘ-TokenTree (annotation x e) = annotation x (parseᵘ-TokenTree e)

  print-TokenTree : 大MonadHom (_ , TokenTree 𝒹) ((_ , TokenExpr (δ 𝒹)))
  print-TokenTree = record { fst = id ; snd = (λ _ -> printᵘ-TokenTree) since {!!} }

  isInferHom:print-TokenTree : isInferHom print-TokenTree
  isInferHom:print-TokenTree = record
    { inferF = id
    ; infer = (λ x → parseᵘ-TokenTree) since {!!}
    ; eval-infer = (λ x → id) since {!!}
    }

  infer-TokenTree : TokenTreeInfer 𝒹 ⟶ TokenExprInfer (δ 𝒹)
  infer-TokenTree = subcathom print-TokenTree isInferHom:print-TokenTree

  -- TokenTreeInferenceTask : InferenceTask _
  -- TokenTreeInferenceTask = inferenceTask (TokenExprInfer (δ 𝒹)) {!!} (TokenTreeInfer 𝒹) infer-TokenTree
  -- TokenTreeInferenceTask = inferenceTask (TokenExprInfer (δ 𝒹)) (hasTextInfer:TokenExpr (δ 𝒹)) (TokenTreeInfer 𝒹) infer-TokenTree




