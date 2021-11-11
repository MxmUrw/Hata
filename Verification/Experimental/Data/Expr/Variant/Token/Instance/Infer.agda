
module Verification.Experimental.Data.Expr.Variant.Token.Instance.Infer where

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


open import Verification.Experimental.Data.Expr.Variant.List.Definition

open import Verification.Experimental.Data.Expr.Variant.Token.Data
open import Verification.Experimental.Data.Expr.Variant.Token.Definition
open import Verification.Experimental.Data.Expr.Variant.Token.Instance.Monad




module _ {𝒹 : TokenExprData} where

  ----------------------------------------------------------
  -- printing the tokenExpressions to listExpressions
  mutual
    print-TokenExprs : ∀{X} -> List (TokenExpr 𝒹 X) -> List (ListExpr X)
    print-TokenExprs [] = []
    print-TokenExprs (x ∷ xs) = print-TokenExpr x ∷ print-TokenExprs xs

    print-TokenExpr : ∀{X} -> TokenExpr 𝒹 X -> ListExpr X
    print-TokenExpr (var x) = var x
    print-TokenExpr (hole x) = hole x
    print-TokenExpr (token x) = var (tokenName 𝒹 x)
    print-TokenExpr (list x) = list (print-TokenExprs x)

  ----------------------------------------------------------
  -- parsing the tokenExpressions from listExpressions

  private
    findToken : Text -> Maybe (TokenType 𝒹)
    findToken name with filter (λ x → tokenName 𝒹 x ≟ name) (tokenList 𝒹)
    ... | [] = nothing
    ... | x ∷ [] = just x
    ... | x ∷ x₁ ∷ X = just x

  mutual
    parse-TokenExprs : ∀{X} -> List (ListExpr X) -> List (TokenExpr 𝒹 (ListExpr X))
    parse-TokenExprs [] = []
    parse-TokenExprs (x ∷ xs) = parse-TokenExpr x ∷ parse-TokenExprs xs

    parse-TokenExpr : ∀{X} -> ListExpr X -> TokenExpr 𝒹 (ListExpr X)
    parse-TokenExpr (var x) = case findToken x of
                                     (λ _ -> var x)
                                     λ x → token x
    parse-TokenExpr (hole x) = hole (hole x)
    parse-TokenExpr (list x) = list (parse-TokenExprs x)




