
module Verification.Core.Data.Expr.Variant.AnnotatedList.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Algebra.Pointed.Definition
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
open import Verification.Core.Data.Expr.Variant.AnnotatedList.Definition


module _ {Ann : 𝐏𝐭𝐝₀} where
  mutual
    map-AListExprs : ∀{A B} -> (A -> B) -> List (AListExpr Ann A) -> List (AListExpr Ann B)
    map-AListExprs f [] = []
    map-AListExprs f (x ∷ xs) = map-AListExpr f x ∷ map-AListExprs f xs

    map-AListExpr : ∀{A B} -> (A -> B) -> AListExpr Ann A -> AListExpr Ann B
    map-AListExpr f (var a x) = var a x
    map-AListExpr f (hole x) = hole (f x)
    map-AListExpr f (list ann x) = list ann (map-AListExprs f x)
    -- map-AListExpr f (annotation x xs) = annotation x (map-AListExpr f xs)

  instance
    isFunctor:AListExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (AListExpr Ann)
    isFunctor.map isFunctor:AListExpr = map-AListExpr
    isFunctor.isSetoidHom:map isFunctor:AListExpr = {!!}
    isFunctor.functoriality-id isFunctor:AListExpr = {!!}
    isFunctor.functoriality-◆ isFunctor:AListExpr = {!!}

  pure-AListExpr : ∀ A -> A -> AListExpr Ann A
  pure-AListExpr _ = hole

  mutual
    join-AListExprs : ∀ A -> List (AListExpr Ann (AListExpr Ann A)) -> List (AListExpr Ann A)
    join-AListExprs _ [] = []
    join-AListExprs _ (x ∷ xs) = join-AListExpr _ x ∷ join-AListExprs _ xs

    join-AListExpr : ∀ A -> AListExpr Ann (AListExpr Ann A) -> AListExpr Ann A
    join-AListExpr _ (var a x) = var a x
    join-AListExpr _ (hole xs) = xs
    join-AListExpr _ (list ann x) = list ann (join-AListExprs _ x)
    -- join-AListExpr _ (annotation x xs) = annotation x (join-AListExpr _ xs)

  instance
    isMonad:AListExpr : isMonad (AListExpr Ann)
    isMonad.pure isMonad:AListExpr = pure-AListExpr
    isMonad.join isMonad:AListExpr = join-AListExpr
    isMonad.isNatural:pure isMonad:AListExpr = {!!}
    isMonad.isNatural:join isMonad:AListExpr = {!!}
    isMonad.unit-l-join isMonad:AListExpr = {!!}
    isMonad.unit-r-join isMonad:AListExpr = {!!}
    isMonad.assoc-join isMonad:AListExpr = {!!}





module _ (Ann : 𝐏𝐭𝐝₀) where

  AListExprInfer : 𝐈𝐧𝐟𝐞𝐫 _
  AListExprInfer = incl (_ , AListExpr Ann)



module _ {Ann : 𝐏𝐭𝐝₀} where
  open import Verification.Core.Data.SourceCode.Variant.HaskellLike.Definition
  instance
    hasTextInfer:AListExprInfer : {{_ : IShow ⟨ Ann ⟩}} -> hasTextInfer (AListExprInfer Ann)
    hasTextInfer:AListExprInfer = record
      { RepObj = ⊤-𝒰
      ; TIObj = Text
      ; RepType = AListExpr Ann Text since isSetoid:byDiscrete
      ; rep = ((λ f → f tt) since {!!}) since record { inverse-◆ = (λ x x₁ → x) since {!!} ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }
      ; parse = λ x → map makeAListExprᵘ (parseHaskellLikeSourceCode x)
      }

module _ (Ann : 𝐏𝐭𝐝₀) where
  AListExprInferenceTask : {{_ : IShow ⟨ Ann ⟩}} -> InferenceTask _
  AListExprInferenceTask = inferenceTask (AListExprInfer Ann) hasTextInfer:AListExprInfer (AListExprInfer Ann) id
