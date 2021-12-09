
module Verification.Core.Data.Expr.Variant.List.Instance.Monad where

open import Verification.Conventions hiding (ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
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

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task
open import Verification.Core.Theory.Std.Inference.TextInfer

-- open import Verification.Core.Data.Expr.Variant.List.Data
open import Verification.Core.Data.Expr.Variant.List.Definition


mutual
  map-ListExprs : ∀{A B} -> (A -> B) -> List (ListExpr A) -> List (ListExpr B)
  map-ListExprs f [] = []
  map-ListExprs f (x ∷ xs) = map-ListExpr f x ∷ map-ListExprs f xs

  map-ListExpr : ∀{A B} -> (A -> B) -> ListExpr A -> ListExpr B
  map-ListExpr f (var x) = var x
  map-ListExpr f (hole x) = hole (f x)
  map-ListExpr f (list x) = list (map-ListExprs f x)
  map-ListExpr f (annotation x xs) = annotation x (map-ListExpr f xs)

instance
  isFunctor:ListExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (ListExpr)
  isFunctor.map isFunctor:ListExpr = map-ListExpr
  isFunctor.isSetoidHom:map isFunctor:ListExpr = {!!}
  isFunctor.functoriality-id isFunctor:ListExpr = {!!}
  isFunctor.functoriality-◆ isFunctor:ListExpr = {!!}

pure-ListExpr : ∀ A -> A -> ListExpr A
pure-ListExpr _ = hole

mutual
  join-ListExprs : ∀ A -> List (ListExpr (ListExpr A)) -> List (ListExpr A)
  join-ListExprs _ [] = []
  join-ListExprs _ (x ∷ xs) = join-ListExpr _ x ∷ join-ListExprs _ xs

  join-ListExpr : ∀ A -> ListExpr (ListExpr A) -> ListExpr A
  join-ListExpr _ (var x) = var x
  join-ListExpr _ (hole xs) = xs
  join-ListExpr _ (list x) = list (join-ListExprs _ x)
  join-ListExpr _ (annotation x xs) = annotation x (join-ListExpr _ xs)

instance
  isMonad:ListExpr : isMonad (ListExpr)
  isMonad.pure isMonad:ListExpr = pure-ListExpr
  isMonad.join isMonad:ListExpr = join-ListExpr
  isMonad.isNatural:pure isMonad:ListExpr = {!!}
  isMonad.isNatural:join isMonad:ListExpr = {!!}
  isMonad.unit-l-join isMonad:ListExpr = {!!}
  isMonad.unit-r-join isMonad:ListExpr = {!!}
  isMonad.assoc-join isMonad:ListExpr = {!!}

ListExprInfer : 𝐈𝐧𝐟𝐞𝐫 _
ListExprInfer = incl (_ , ListExpr)


open import Verification.Core.Data.SourceCode.Variant.HaskellLike.Definition
instance
  hasTextInfer:ListExprInfer : hasTextInfer ListExprInfer
  hasTextInfer:ListExprInfer = record
    { RepObj = ⊤-𝒰
    ; TIObj = Text
    ; RepType = ListExpr Text since isSetoid:byDiscrete
    ; rep = ((λ f → f tt) since {!!}) since record { inverse-◆ = (λ x x₁ → x) since {!!} ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }
    ; parse = λ x → map makeListExprᵘ (parseHaskellLikeSourceCode x)
    }


ListExprInferenceTask : InferenceTask _
ListExprInferenceTask = inferenceTask ListExprInfer hasTextInfer:ListExprInfer ListExprInfer id



