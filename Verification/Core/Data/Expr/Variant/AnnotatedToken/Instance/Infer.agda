
module Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Infer where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category

open import Verification.Core.Algebra.AllOf.Pointed

open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
-- open import Verification.Core.Data.AllOf.Product
-- open import Verification.Core.Data.AllOf.Sum
-- open import Verification.Core.Data.Expr.Variant.Base.Definition
-- open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
-- open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Opposite
-- open import Verification.Core.Category.Std.Category.Construction.Product
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
-- open import Verification.Core.Category.Std.Limit.Specific.Product
-- open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
-- open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Constant
-- open import Verification.Core.Category.Std.Morphism.Iso
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
open import Verification.Core.Data.Expr.Variant.AnnotatedList.Instance.Monad
-- open import Verification.Core.Data.Expr.Variant.AnnotatedList.Instance.Infer

open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Definition
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Monad


instance
  IShow:ATokenExprAnnᵈ : IShow ATokenExprAnnᵈ
  IShow:ATokenExprAnnᵈ = record { show = lem-1 }
    where
      lem-1 : ATokenExprAnnᵈ → Text
      lem-1 isvar = "var"
      lem-1 istoken = "token"


module _ {𝒹 : ATokenExprData} {Ann : 𝐏𝐭𝐝₀} where

  private
    Ann' : 𝐏𝐭𝐝₀
    Ann' = Ann × ATokenExprAnn

  ----------------------------------------------------------
  -- printing the tokenExpressions to listExpressions
  mutual
    print-ATokenExprᵘs : ∀{X n} -> ConstDList (ATokenExpr 𝒹 Ann X) n -> List (AListExpr (Ann') X)
    print-ATokenExprᵘs [] = []
    print-ATokenExprᵘs (x ∷ xs) = print-ATokenExprᵘ x ∷ print-ATokenExprᵘs xs

    print-ATokenExprᵘ : ∀{X} -> ATokenExpr 𝒹 Ann X -> AListExpr Ann' X
    print-ATokenExprᵘ (var ann x) = var (ann , (just isvar)) x
    print-ATokenExprᵘ (hole x) = hole x
    print-ATokenExprᵘ (token ann x) = var (ann , (just istoken)) (tokenName 𝒹 x)
    print-ATokenExprᵘ (list x) = list (print-ATokenExprᵘs x)
    -- print-ATokenExprᵘ (annotation t x) = annotation t (print-ATokenExprᵘ x)

  print-ATokenExpr : 大MonadHom (_ , ATokenExpr 𝒹 Ann) (_ , AListExpr Ann')
  print-ATokenExpr = record { fst = id ; snd = (λ _ -> print-ATokenExprᵘ) since {!!} }

  ----------------------------------------------------------
  -- parsing the tokenExpressions from listExpressions

  private
    findToken : Text -> Maybe (TokenType 𝒹)
    findToken name with filter (λ x → tokenName 𝒹 x ≟ name) (tokenList 𝒹)
    ... | [] = nothing
    ... | x ∷ [] = just x
    ... | x ∷ x₁ ∷ X = just x

  mutual
    parse-ATokenExprs : ∀{X} -> List (AListExpr Ann' X) -> ∑ ConstDList (ATokenExpr 𝒹 Ann (AListExpr Ann' X))
    parse-ATokenExprs [] = _ , []
    parse-ATokenExprs (x ∷ xs) = (tt ∷ _) , parse-ATokenExpr x ∷ parse-ATokenExprs xs .snd

    parse-ATokenExpr : ∀{X} -> AListExpr Ann' X -> ATokenExpr 𝒹 Ann (AListExpr Ann' X)
    parse-ATokenExpr (var (ann , _) x) = case findToken x of
                                     (λ _ -> var ann x)
                                     λ x → token ann x
    parse-ATokenExpr (hole x) = hole (hole x)
    parse-ATokenExpr (list x) = list (parse-ATokenExprs x .snd)

    -- parse-ATokenExpr (annotation t x) = annotation t (parse-ATokenExpr x)

  isInferHom:print-ATokenExpr : isInferHom (print-ATokenExpr)
  isInferHom:print-ATokenExpr = record
    { inferF = id
    ; infer = (λ _ -> parse-ATokenExpr) since {!!}
    ; eval-infer = {!!}
    }



  -- the inference task

  ATokenExprInferenceTask : {{_ : IShow ⟨ Ann ⟩}} -> InferenceTask _
  ATokenExprInferenceTask = inferenceTask (AListExprInfer Ann') (hasTextInfer:AListExprInfer)
                                          (ATokenExprInfer 𝒹 Ann)
                                          (subcathom print-ATokenExpr isInferHom:print-ATokenExpr)


