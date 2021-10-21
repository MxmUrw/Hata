
module Verification.Experimental.Data.Expr.Variant.Base.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Constant
open import Verification.Experimental.Set.Setoid.As.Category

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.Category
open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.TextInfer



instance
  isSetoid:BaseExprParam : isSetoid BaseExprParam
  isSetoid:BaseExprParam = isSetoid:byStrId

  isCategory:BaseExprParam : isCategory BaseExprParam
  isCategory:BaseExprParam = isCategory:bySetoid {𝑘 = ℓ₀}

module _ {P : BaseExprParam} where
  instance
    isFunctor:BaseExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (BaseExpr P)
    isFunctor.map isFunctor:BaseExpr = {!!}
    isFunctor.isSetoidHom:map isFunctor:BaseExpr = {!!}
    isFunctor.functoriality-id isFunctor:BaseExpr = {!!}
    isFunctor.functoriality-◆ isFunctor:BaseExpr = {!!}

  instance
    isMonad:BaseExpr : isMonad (BaseExpr P)
    isMonad:BaseExpr = {!!}

  instance
    hasTextInfer:BaseExpr : hasTextInfer (BaseExpr P)
    hasTextInfer.TIObj hasTextInfer:BaseExpr = ⊤-𝒰
    hasTextInfer.parse hasTextInfer:BaseExpr = parseBaseExpr
    hasTextInfer.IShow:TI hasTextInfer:BaseExpr = it



-------------------------
-- Building a monad from a parametrized monad

open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition

module _ {𝒞 : Category 𝑖} {𝒫 : Category 𝑗} {T : ⟨ 𝒫 ⟩ -> Monad 𝒞} where
  private
    F : Functor (𝒫 ᵒᵖ) (𝐂𝐚𝐭 _)
    F = Const 𝒞

    ℰ : Category _
    ℰ = ⨊ᵒᵖ F

    Sᵘ : ⟨ ℰ ⟩ -> ⟨ ℰ ⟩
    Sᵘ (a , a⃨) = a , (⟨ T a ⟩ a⃨)

    macro S = #structureOn Sᵘ

    map-S : ∀{a b} -> a ⟶ b -> S a ⟶ S b
    map-S {a} {b} (f , f⃨) = g , {!!}
      where
        g : base (S a) ⟶ base (S b)
        g = f

    instance
      isFunctor:S : isFunctor ℰ ℰ S
      isFunctor.map isFunctor:S = {!!}
      isFunctor.isSetoidHom:map isFunctor:S = {!!}
      isFunctor.functoriality-id isFunctor:S = {!!}
      isFunctor.functoriality-◆ isFunctor:S = {!!}

    -- aaaaa = isFunctor:const

    -- 𝒟 : Category _
    -- 𝒟 = {!!}



-- 大𝐌𝐧𝐝>BaseExpr : 大𝐌𝐧𝐝 _
-- 大𝐌𝐧𝐝>BaseExpr = {!!} , {!!}



