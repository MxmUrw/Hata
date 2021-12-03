
module Verification.Core.Data.Tree.Variant.AnnotatedToken.Instance.Infer where


open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Algebra.AllOf.Pointed
open import Verification.Core.Set.AllOf.Setoid
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Inference.Definition

open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task

open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Definition
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Monad

open import Verification.Core.Data.Tree.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Tree.Variant.AnnotatedToken.Definition
open import Verification.Core.Data.Tree.Variant.AnnotatedToken.Instance.Monad



toATokenExprData : ATokenTreeData -> ATokenExprData
toATokenExprData 𝒹 = record { TokenType = TokenType 𝒹 ; tokenName = tokenName 𝒹 ; tokenList = tokenList 𝒹 }

private
  δ = toATokenExprData


module _ {𝒹 : ATokenTreeData} {Ann : 𝐏𝐭𝐝₀} where
  private
    Ann' : 𝐏𝐭𝐝₀
    Ann' = Ann × ATokenTreeAnn 𝒹

  mutual
    printᵘ-TokenTrees : ∀{A n} -> ConstListᴰ (ATokenTree 𝒹 Ann A) n -> ConstListᴰ (ATokenExpr (δ 𝒹) Ann' A) n
    printᵘ-TokenTrees [] = []
    printᵘ-TokenTrees (x ∷ xs) = (printᵘ-TokenTree x) ∷ (printᵘ-TokenTrees xs)

    printᵘ-TokenTree : ∀{A} -> ATokenTree 𝒹 Ann A -> ATokenExpr (δ 𝒹) Ann' A
    printᵘ-TokenTree (hole x) = hole x
    printᵘ-TokenTree (var ann x) = var (ann , just isvar) x
    printᵘ-TokenTree (node ann t x) = list (ann , just istoken) (_∷_ {a = tt} (token (ann , just istoken) t) (printᵘ-TokenTrees x))




  mutual
    parseᵘ-TokenTrees : ∀{A n} -> ConstListᴰ (ATokenExpr (δ 𝒹) Ann' A) n -> ConstListᴰ (ATokenTree 𝒹 Ann (ATokenExpr (δ 𝒹) Ann' A)) n
    parseᵘ-TokenTrees [] = []
    parseᵘ-TokenTrees (x ∷ xs) = (parseᵘ-TokenTree x) ∷ (parseᵘ-TokenTrees xs)

    parseᵘ-TokenTree : ∀{A} -> ATokenExpr (δ 𝒹) Ann' A -> ATokenTree 𝒹 Ann (ATokenExpr (δ 𝒹) Ann' A)
    parseᵘ-TokenTree (hole x) = hole (hole x)
    parseᵘ-TokenTree (var (ann , _) x) = var ann x
    parseᵘ-TokenTree (token (ann , _) x) with tokenSize 𝒹 x ≟-Str 0
    ... | yes p = node {!!} (x) (transport-Str (cong-Str (λ ξ -> ConstListᴰ (ATokenTree 𝒹 Ann (ATokenExpr (δ 𝒹) Ann' _)) ξ) (sym-≣ p)) [])
    ... | no ¬p = hole (token (ann , just (iserror ("Need " <> show (tokenSize 𝒹 (x)) <> " arguments here."))) x)
    -- (annotation ("This token has " <> show (tokenSize 𝒹 (x)) <> " arguments, but has been applied to none.")
    --                                (token x))
    parseᵘ-TokenTree (list {[]} (ann , _) []) = hole (list (ann , just (iserror "Empty expression!")) []) -- (annotation "Empty expressions are not allowed." (list []))
    parseᵘ-TokenTree (list {tt ∷ n} (ann , _) (token ann2 x ∷ xs)) with tokenSize 𝒹 (x) ≟-Str n
    ... | yes refl-≣ = node ann (x) (parseᵘ-TokenTrees xs)
    ... | no ¬p = hole ((list (ann , just (iserror "wrong number of args")) (_∷_ {a = tt} (token (ann , just istoken) x) xs))) -- (annotation ("This token has " <> show (tokenSize 𝒹 (x)) <> " arguments, but has been applied to " <> show n <> ".")

                                   -- ((list (_∷_ {a = tt} (token x) xs))))
    parseᵘ-TokenTree (list {tt ∷ n} (ann , _) (x ∷ xs)) = hole ((list (ann , just (iserror "First element no token!")) (_∷_ {a = tt} x xs))) --  (annotation "The first element of an expression has to be a token." (list (_∷_ {a = tt} x xs)))
    -- parseᵘ-TokenTree (annotation x e) = annotation x (parseᵘ-TokenTree e)

  print-TokenTree : 大MonadHom (_ , ATokenTree 𝒹 Ann) ((_ , ATokenExpr (δ 𝒹) Ann'))
  print-TokenTree = record { fst = id ; snd = (λ _ -> printᵘ-TokenTree) since {!!} }

  isInferHom:print-TokenTree : isInferHom print-TokenTree
  isInferHom:print-TokenTree = record
    { inferF = id
    ; infer = (λ x → parseᵘ-TokenTree) since {!!}
    ; eval-infer = (λ x → {!!}) since {!!}
    }

  infer-TokenTree : ATokenTreeInfer 𝒹 Ann ⟶ ATokenExprInfer (δ 𝒹) Ann'
  infer-TokenTree = subcathom print-TokenTree isInferHom:print-TokenTree

  -- TokenTreeInferenceTask : InferenceTask _
  -- TokenTreeInferenceTask = inferenceTask (ATokenExprInfer (δ 𝒹)) {!!} (TokenTreeInfer 𝒹) infer-TokenTree
  -- TokenTreeInferenceTask = inferenceTask (ATokenExprInfer (δ 𝒹)) (hasTextInfer:ATokenExpr (δ 𝒹) Ann') (TokenTreeInfer 𝒹) infer-TokenTree




  open import Verification.Core.Data.Expr.Variant.AnnotatedList.Definition
  open import Verification.Core.Data.Expr.Variant.AnnotatedList.Instance.Monad
  open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Infer

  ATokenTreeInferenceTask : {{_ : IShow ⟨ Ann ⟩}} -> InferenceTask _
  ATokenTreeInferenceTask = inferenceTask (AListExprInfer _) (hasTextInfer:AListExprInfer)
                                          (ATokenTreeInfer 𝒹 Ann)
                                          -- let f = (infer-TokenExpr {𝒹 = δ 𝒹} {Ann = {!!}})
                                           (infer-TokenTree ◆ infer-TokenExpr)
                                          -- (subcathom print-ATokenExpr isInferHom:print-ATokenExpr)

