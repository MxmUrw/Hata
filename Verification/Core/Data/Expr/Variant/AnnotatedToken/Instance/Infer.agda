
module Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Infer where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Everything
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


open import Verification.Core.Data.Expr.Variant.AnnotatedList.Definition

open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Definition
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Monad




module _ {𝒹 : ATokenExprData} {Ann} where

  ----------------------------------------------------------
  -- printing the tokenExpressions to listExpressions
  mutual
    print-ATokenExprs : ∀{X n} -> ConstDList (ATokenExpr 𝒹 Ann X) n -> List (AListExpr {!!} X)
    print-ATokenExprs [] = []
    print-ATokenExprs (x ∷ xs) = print-ATokenExpr x ∷ print-ATokenExprs xs

    print-ATokenExpr : ∀{X} -> ATokenExpr 𝒹 Ann X -> AListExpr {!!} X
    print-ATokenExpr (var ann x) = var {!!} x
    print-ATokenExpr (hole x) = hole x
    print-ATokenExpr (token ann x) = var {!!} (tokenName 𝒹 x)
    print-ATokenExpr (list x) = list (print-ATokenExprs x)
    -- print-ATokenExpr (annotation t x) = annotation t (print-ATokenExpr x)


  ----------------------------------------------------------
  -- parsing the tokenExpressions from listExpressions

  private
    findToken : Text -> Maybe (TokenType 𝒹)
    findToken name with filter (λ x → tokenName 𝒹 x ≟ name) (tokenList 𝒹)
    ... | [] = nothing
    ... | x ∷ [] = just x
    ... | x ∷ x₁ ∷ X = just x

  mutual
    parse-ATokenExprs : ∀{X} -> List (AListExpr {!!} X) -> ∑ ConstDList (ATokenExpr 𝒹 Ann (AListExpr {!!} X))
    parse-ATokenExprs [] = _ , []
    parse-ATokenExprs (x ∷ xs) = (tt ∷ _) , parse-ATokenExpr x ∷ parse-ATokenExprs xs .snd

    parse-ATokenExpr : ∀{X} -> AListExpr {!!} X -> ATokenExpr 𝒹 Ann (AListExpr {!!} X)
    parse-ATokenExpr (var ann x) = case findToken x of
                                     (λ _ -> var {!!} x)
                                     λ x → token {!!} x
    parse-ATokenExpr (hole x) = hole (hole x)
    parse-ATokenExpr (list x) = list (parse-ATokenExprs x .snd)
    -- parse-ATokenExpr (annotation t x) = annotation t (parse-ATokenExpr x)



