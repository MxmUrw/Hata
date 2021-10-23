
module Verification.Experimental.Data.Expr.Variant.Base.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Constant
open import Verification.Experimental.Set.Setoid.As.Category
open import Verification.Experimental.Set.Setoid.Definition

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

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso


module _ {𝒞 : Category 𝑖} {𝒫 : Category 𝑗} {T : Functor 𝒫 (𝐌𝐧𝐝 𝒞)} where
  private
    F : Functor (𝒫 ᵒᵖ) (𝐂𝐚𝐭 _)
    F = Const 𝒞

    ℰ : Category _
    ℰ = ⨊ᵒᵖ F

    Dᵘ : ⟨ ℰ ⟩ -> ⟨ 𝒞 ⟩
    Dᵘ (a , a⃨) = a⃨

    macro D = #structureOn Dᵘ

    map-D : ∀{a b} -> a ⟶ b -> D a ⟶ D b
    map-D (f , f⃨) = f⃨

    instance
      isSetoidHom:map-D : ∀{a b} -> isSetoidHom (a ⟶ b) (D a ⟶ D b) map-D
      isSetoidHom.cong-∼ (isSetoidHom:map-D {a} {b}) {f , f⃨} {g , g⃨} (p , p⃨) = unit-r-◆ ⁻¹ ∙ p⃨


    isFunctor:D : isFunctor ℰ 𝒞 D
    isFunctor.map isFunctor:D = map-D
    isFunctor.isSetoidHom:map isFunctor:D = it
    isFunctor.functoriality-id isFunctor:D = refl
    isFunctor.functoriality-◆ isFunctor:D = {!!}

    -- Sᵘ : ⟨ ℰ ⟩ -> ⟨ ℰ ⟩
    -- Sᵘ (a , a⃨) = a , (⟨ ⟨ T ⟩ a ⟩ a⃨)

    -- macro S = #structureOn Sᵘ

    -- map-S : ∀{a b} -> a ⟶ b -> S a ⟶ S b
    -- map-S {a} {b} (f , f⃨) = g , g⃨
    --   where
    --     g : base (S a) ⟶ base (S b)
    --     g = f

    --     g⃨ : ⟨ ⟨ T ⟩ (base a) ⟩ (fib a) ⟶ ⟨ ⟨ T ⟩ (base b) ⟩ (fib b)
    --     g⃨ = mapOf (↳ ⟨ T ⟩ (base a)) f⃨ ◆ ⟨ ⟨ mapOf T f ⟩ ⟩ (fib b)

    -- instance
    --   isSetoidHom:map-S : ∀{a} {b} -> isSetoidHom (a ⟶ b) (S a ⟶ S b) (map-S)
    --   isSetoidHom.cong-∼ (isSetoidHom:map-S {a} {b}) {f , f⃨} {g , g⃨} (p , p⃨) = p , q⃨
    --     where
    --       q⃨ : (isCategory.isSetoid:Hom (_:&_.of ⟨ F ⟩ (base (Sᵘ a)))
    --           isSetoid.∼
    --           ((_:&_.of ⟨ F ⟩ (base (Sᵘ a))) isCategory.◆ fib (map-S (f , f⃨)))
    --           (⟨ ⟨ isSetoidHom.cong-∼ (isFunctor.isSetoidHom:map (_:&_.of F)) p ⟩
    --             ⟩
    --             (fib (Sᵘ b))))
    --           (fib (map-S (g , g⃨)))
    --       q⃨ = {!!}
        -- where
        --   q⃨ : mapOf (↳ ⟨ T ⟩ (base a)) f⃨ ◆ ⟨ ⟨ mapOf T f ⟩ ⟩ (fib b) ◆ (⟨ ⟨ cong-∼ p ⟩ ⟩ _)
        --      ∼
        --      mapOf (↳ ⟨ T ⟩ (base a)) g⃨ ◆ ⟨ ⟨ mapOf T g ⟩ ⟩ (fib b)
        --   q⃨ = ?

      -- record { cong-∼ = λ (p , p⃨) → p , {!? ◈ ?!} }

    -- instance
    --   isFunctor:S : isFunctor ℰ ℰ S
    --   isFunctor.map isFunctor:S = map-S
    --   isFunctor.isSetoidHom:map isFunctor:S = {!!}
    --   isFunctor.functoriality-id isFunctor:S = {!!}
    --   isFunctor.functoriality-◆ isFunctor:S = {!!}

    -- open ShortMonadNotation

    -- pure-S : ∀(a) -> a ⟶ S a
    -- pure-S (a , a⃨) = id , ⟨ ηOf (⟨ T ⟩ a) ⟩ a⃨

    -- instance

    --   isMonad:S : isMonad S
    --   isMonad.pure isMonad:S = pure-S
    --   isMonad.join isMonad:S = {!!}
    --   isMonad.isNatural:pure isMonad:S = {!!}
    --   isMonad.isNatural:join isMonad:S = {!!}
    --   isMonad.unit-l-join isMonad:S = {!!}
    --   isMonad.unit-r-join isMonad:S = {!!}
    --   isMonad.assoc-join isMonad:S = {!!}

    -- aaaaa = isFunctor:const

    -- 𝒟 : Category _
    -- 𝒟 = {!!}



-- 大𝐌𝐧𝐝>BaseExpr : 大𝐌𝐧𝐝 _
-- 大𝐌𝐧𝐝>BaseExpr = {!!} , {!!}



