
module Verification.Core.Data.Tree.Variant.Token.Instance.Infer where

open import Verification.Conventions hiding (ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Set.Setoid.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task

open import Verification.Core.Data.Expr.Variant.Token.Data
open import Verification.Core.Data.Expr.Variant.Token.Definition
open import Verification.Core.Data.Expr.Variant.Token.Instance.Monad

open import Verification.Core.Data.Tree.Variant.Token.Data
open import Verification.Core.Data.Tree.Variant.Token.Definition
open import Verification.Core.Data.Tree.Variant.Token.Instance.Monad

open import Verification.Core.Data.Substitution.Variant.Normal.Definition

-- open import Verification.Core.Data.SourceCode.Variant.Tokenized.Definition
-- open import Verification.Core.Data.Expr.Variant.Base.Definition
-- open import Verification.Core.Data.Expr.Variant.Base.Instance.Monad

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
    printᵘ-TokenTrees : ∀{A n} -> ConstListᴰ (TokenTree 𝒹 A) n -> ConstListᴰ (TokenExpr (δ 𝒹) A) n
    printᵘ-TokenTrees [] = []
    printᵘ-TokenTrees (x ∷ xs) = (printᵘ-TokenTree x) ∷ (printᵘ-TokenTrees xs)

    printᵘ-TokenTree : ∀{A} -> TokenTree 𝒹 A -> TokenExpr (δ 𝒹) A
    printᵘ-TokenTree (hole x) = hole x
    printᵘ-TokenTree (var x) = var x
    printᵘ-TokenTree (node t x) = list (_∷_ {a = tt} (token t) (printᵘ-TokenTrees x))
    printᵘ-TokenTree (annotation x e) = annotation x (printᵘ-TokenTree e)


  mutual
    parseᵘ-TokenTrees : ∀{A n} -> ConstListᴰ (TokenExpr (δ 𝒹) A) n -> ConstListᴰ (TokenTree 𝒹 (TokenExpr (δ 𝒹) A)) n
    parseᵘ-TokenTrees [] = []
    parseᵘ-TokenTrees (x ∷ xs) = (parseᵘ-TokenTree x) ∷ (parseᵘ-TokenTrees xs)

    parseᵘ-TokenTree : ∀{A} -> TokenExpr (δ 𝒹) A -> TokenTree 𝒹 (TokenExpr (δ 𝒹) A)
    parseᵘ-TokenTree (hole x) = hole (hole x)
    parseᵘ-TokenTree (var x) = var x
    parseᵘ-TokenTree (token x) with tokenSize 𝒹 x ≟-Str 0
    ... | yes p = node (x) (transport-Str (cong-Str (λ ξ -> ConstListᴰ (TokenTree 𝒹 (TokenExpr (δ 𝒹) _)) ξ) (sym-≣ p)) [])
    ... | no ¬p = hole (annotation ("This token has " <> show (tokenSize 𝒹 (x)) <> " arguments, but has been applied to none.")
                                   (token x))
    parseᵘ-TokenTree (list {[]} []) = hole (annotation "Empty expressions are not allowed." (list []))
    parseᵘ-TokenTree (list {tt ∷ n} (token x ∷ xs)) with tokenSize 𝒹 (x) ≟-Str n
    ... | yes refl-≣ = node (x) (parseᵘ-TokenTrees xs)
    ... | no ¬p = hole (annotation ("This token has " <> show (tokenSize 𝒹 (x)) <> " arguments, but has been applied to " <> show n <> ".")
                                   ((list (_∷_ {a = tt} (token x) xs))))
    parseᵘ-TokenTree (list {tt ∷ n} (x ∷ xs)) = hole (annotation "The first element of an expression has to be a token." (list (_∷_ {a = tt} x xs)))
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




