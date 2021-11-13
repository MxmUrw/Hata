
module Verification.Core.Data.Expr.Variant.Base.Instance.Monad where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Everything
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
open import Verification.Core.Theory.Std.Inference.TextInfer

{-

module _ {A : 𝒰 𝑖} {a b : A} where
  instance
    isSetoid:≣ : isSetoid (a ≣ b)
    isSetoid:≣ = isSetoid:byDiscrete

instance
  isSetoid:BaseExprData : isSetoid BaseExprData
  isSetoid:BaseExprData = isSetoid:byDiscrete

  isCategory:BaseExprData : isCategory BaseExprData
  isCategory:BaseExprData = isCategory:bySetoid

module _ {P : BaseExprData} where
  mutual
    map-BaseExprs : ∀{A B} -> (A -> B) -> Vec (BaseExpr P A) n -> Vec (BaseExpr P B) n
    map-BaseExprs f [] = []
    map-BaseExprs f (x ∷ xs) = map-BaseExpr f x ∷ map-BaseExprs f xs

    map-BaseExpr : ∀{A B} -> (A -> B) -> BaseExpr P A -> BaseExpr P B
    map-BaseExpr f (hole x) = hole (f x)
    map-BaseExpr f (var x) = var x
    map-BaseExpr f (token x) = token x
    map-BaseExpr f (list x) = list (map-BaseExprs f x)
    map-BaseExpr f (annotation x expr) = map-BaseExpr f expr

  instance
    isFunctor:BaseExpr : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (BaseExpr P)
    isFunctor.map isFunctor:BaseExpr = map-BaseExpr
    isFunctor.isSetoidHom:map isFunctor:BaseExpr = {!!}
    isFunctor.functoriality-id isFunctor:BaseExpr = {!!}
    isFunctor.functoriality-◆ isFunctor:BaseExpr = {!!}

  pure-BaseExpr : ∀(A) -> A -> BaseExpr P A
  pure-BaseExpr _ = hole

  mutual
    join-BaseExprs : ∀(A) -> Vec (BaseExpr P (BaseExpr P A)) n -> Vec (BaseExpr P A) n
    join-BaseExprs _ [] = []
    join-BaseExprs _ (x ∷ xs) = join-BaseExpr _ x ∷ join-BaseExprs _ xs

    join-BaseExpr : ∀(A) -> BaseExpr P (BaseExpr P A) -> BaseExpr P A
    join-BaseExpr _ (hole expr) = expr
    join-BaseExpr _ (var x) = var x
    join-BaseExpr _ (token x) = token x
    join-BaseExpr _ (list x) = list (join-BaseExprs _ x)
    join-BaseExpr _ (annotation x expr) = join-BaseExpr _ expr

  instance
    isMonad:BaseExpr : isMonad (BaseExpr P)
    isMonad.pure isMonad:BaseExpr = pure-BaseExpr
    isMonad.join isMonad:BaseExpr = join-BaseExpr
    isMonad.isNatural:pure isMonad:BaseExpr = {!!}
    isMonad.isNatural:join isMonad:BaseExpr = {!!}
    isMonad.unit-l-join isMonad:BaseExpr = {!!}
    isMonad.unit-r-join isMonad:BaseExpr = {!!}
    isMonad.assoc-join isMonad:BaseExpr = {!!}

  -- instance
  --   hasTextInfer:BaseExpr : hasTextInfer (BaseExpr P)
  --   hasTextInfer.TIObj hasTextInfer:BaseExpr = ⊤-𝒰
  --   hasTextInfer.parse hasTextInfer:BaseExpr = parseBaseExpr
  --   hasTextInfer.IShow:TI hasTextInfer:BaseExpr = it



-------------------------
-- Building a monad from a parametrized monad

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Morphism.Iso


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  infixl 200 _⇂_ _⇂≀_
  _⇂_ : (F : Functor 𝒞 𝒟) -> ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> ⟨ F ⟩ a ⟶ ⟨ F ⟩ b
  _⇂_ F f = map f

  _⇂≀_ : (F : Functor 𝒞 𝒟) -> ∀{a b : ⟨ 𝒞 ⟩} -> {f₀ f₁ : a ⟶ b}
        -> f₀ ∼ f₁ -> F ⇂ f₀ ∼ F ⇂ f₁
  _⇂≀_ F p = cong-∼ p


{-
module _ {𝒞 : Category 𝑖} {𝒫 : Category 𝑗} (T : Functor 𝒫 (𝐌𝐧𝐝 𝒞)) where
  private
    F : Functor (𝒫 ᵒᵖ) (𝐂𝐚𝐭 _)
    F = Const 𝒞

    ℰ : Category _
    ℰ = 𝒫 ×-𝐂𝐚𝐭 𝒞


    Sᵘ : ⟨ ℰ ⟩ -> ⟨ ℰ ⟩
    Sᵘ (a , x) = a , (⟨ ⟨ T ⟩ a ⟩ x)

    macro S = #structureOn Sᵘ

    map-S : ∀{a b} -> a ⟶ b -> S a ⟶ S b
    map-S {a , a⃨} {b , b⃨} (f , f⃨) = f , ((↳ ⟨ T ⟩ a) ⇂ f⃨) ◆ ⟨ ⟨ T ⇂ f ⟩ ⟩ b⃨

    instance
      isSetoidHom:map-S : ∀{a} {b} -> isSetoidHom (a ⟶ b) (S a ⟶ S b) (map-S)
      isSetoidHom.cong-∼ (isSetoidHom:map-S {a , a⃨} {b , b⃨}) {f , f⃨} {g , g⃨} (p , p⃨) = p , q
        where
          q : (↳ ⟨ T ⟩ a) ⇂ f⃨ ◆ ⟨ ⟨ T ⇂ f ⟩ ⟩ b⃨
              ∼
              (↳ ⟨ T ⟩ a) ⇂ g⃨ ◆ ⟨ ⟨ T ⇂ g ⟩ ⟩ b⃨
          q = ((↳ ⟨ T ⟩ a) ⇂≀ p⃨) ◈ ⟨ ⟨ T ⇂≀ p ⟩ ⟩ b⃨

    functoriality-id-S : ∀{a} -> map-S (idOn a) ∼ idOn (S a)
    functoriality-id-S {a , a⃨} = refl , (functoriality-id {{of ↳ ⟨ T ⟩ a}} ◈ ⟨ ⟨ functoriality-id ⟩ ⟩ a⃨ ∙ unit-2-◆)

    functoriality-◆-S : ∀{a b c : ⟨ ℰ ⟩} -> {f : a ⟶ b} {g : b ⟶ c} -> map-S (f ◆ g) ∼ map-S f ◆ map-S g
    functoriality-◆-S {a , a⃨} {b , b⃨} {c , c⃨} {f , f⃨} {g , g⃨} = refl , lem-1
      where
        lem-1 : (↳ ⟨ T ⟩ a) ⇂ (f⃨ ◆ g⃨) ◆ ⟨ ⟨ T ⇂ (f ◆ g) ⟩ ⟩ c⃨
                ∼
                ((↳ ⟨ T ⟩ a) ⇂ f⃨ ◆ ⟨ ⟨ T ⇂ f ⟩ ⟩ b⃨) ◆ ((↳ ⟨ T ⟩ b) ⇂ g⃨ ◆ ⟨ ⟨ T ⇂ g ⟩ ⟩ c⃨)
        lem-1 = {!!}

    instance
      isFunctor:S : isFunctor ℰ ℰ S
      isFunctor.map isFunctor:S = map-S
      isFunctor.isSetoidHom:map isFunctor:S = isSetoidHom:map-S
      isFunctor.functoriality-id isFunctor:S = functoriality-id-S
      isFunctor.functoriality-◆ isFunctor:S = {!!}


    open ShortMonadNotation

    pure-S : ∀(a) -> a ⟶ S a
    pure-S (a , a⃨) = id , ⟨ ηOf (⟨ T ⟩ a) ⟩ a⃨

    instance
      isMonad:S : isMonad S
      isMonad.pure isMonad:S = pure-S
      isMonad.join isMonad:S = {!!}
      isMonad.isNatural:pure isMonad:S = {!!}
      isMonad.isNatural:join isMonad:S = {!!}
      isMonad.unit-l-join isMonad:S = {!!}
      isMonad.unit-r-join isMonad:S = {!!}
      isMonad.assoc-join isMonad:S = {!!}

  ∑Mnd : Monad ℰ
  ∑Mnd = S
-}


--------------
-- functor from discrete categories

module _ {A : 𝒰 𝑖} where
  private
    instance
      isSetoid:A : isSetoid A
      isSetoid:A = isSetoid:byDiscrete

      isCategory:A : isCategory A
      isCategory:A = isCategory:bySetoid

  isFunctor:byDiscrete : ∀{𝒞 : Category 𝑗} -> {f : A -> ⟨ 𝒞 ⟩} -> isFunctor ′ A ′ 𝒞 f
  isFunctor.map isFunctor:byDiscrete = λ {refl-≣ → id}
  isFunctor.isSetoidHom:map isFunctor:byDiscrete = record { cong-∼ = λ {refl-≣ → refl }}
  isFunctor.functoriality-id isFunctor:byDiscrete = refl
  isFunctor.functoriality-◆ isFunctor:byDiscrete {f = refl-≣} {g = refl-≣} = unit-2-◆ ⁻¹




--------------
-- the infer object for BaseExpr
--
-- large monad

BaseExprFᵘ : BaseExprData -> 𝐌𝐧𝐝 (𝐔𝐧𝐢𝐯 ℓ₀)
BaseExprFᵘ 𝒫 = BaseExpr 𝒫

macro BaseExprF = #structureOn BaseExprFᵘ

instance
  isFunctor:BaseExprF : isFunctor ′ BaseExprData ′ (𝐌𝐧𝐝 (𝐔𝐧𝐢𝐯 ℓ₀)) BaseExprF
  isFunctor:BaseExprF = isFunctor:byDiscrete

-- BaseExprMnd = ∑Mnd BaseExprF

BaseExprInfer : BaseExprData -> 𝐈𝐧𝐟𝐞𝐫 _
BaseExprInfer d = incl (_ , BaseExpr d)

hasTextInfer:BaseExpr : (d : BaseExprData) -> hasTextInfer (BaseExprInfer d)
hasTextInfer:BaseExpr d = record
  { RepObj = ⊤-𝒰
  ; TIObj = String
  ; RepType = (BaseExprᵘ d String) since isSetoid:byDiscrete
  ; rep = rep'
  ; parse = parseBaseExpr
  ; IShow:TI = record { show = show }
  }
  where
    rep' : Hom' ′ (⊤-𝒰 → BaseExprᵘ d Text) ′ (BaseExprᵘ d Text since isSetoid:byDiscrete) :& isIso
    rep' = f since P
      where
        f : ′ (⊤-𝒰 → BaseExprᵘ d Text) ′ ⟶ (BaseExprᵘ d Text since isSetoid:byDiscrete)
        f = (λ x → x tt) since record { cong-∼ = λ {x → ≡→≡-Str λ i → x i tt} }

        g : (BaseExprᵘ d Text since isSetoid:byDiscrete) ⟶ ′ (⊤-𝒰 → BaseExprᵘ d Text) ′
        g = (λ x x₁ → x) since record { cong-∼ = λ {refl-≣ → refl-≡} }

        P = record { inverse-◆ = g ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }

-- hasTextInfer:BaseExprMnd : BaseExprData -> hasTextInfer (BaseExprInfer)
-- hasTextInfer:BaseExprMnd p = record
--   { RepObj = p , ⊤-𝒰
--   ; TIObj = p , String
--   ; RepType = Lift (BaseExprᵘ p String) since isSetoid:byDiscrete
--   ; rep = rep'
--   ; parse = λ x → mapRight lift (parseBaseExpr x)
--   ; IShow:TI = record { show = λ x → show (lower x) }
--   }
--   where
--     -- rep' : Hom' ′ Σ (StrId p p) (λ a → ⊤-𝒰 → BaseExprᵘ p ⊤-𝒰) ′
--     --        (Lift (BaseExprᵘ p ⊤-𝒰) since isSetoid:byDiscrete)
--     --        :& isIso
--     rep' : (isCategory.Hom (_:&_.of fst ⟨ BaseExprInfer ⟩) (p , ⊤-𝒰)
--             (⟨ snd ⟨ BaseExprInfer ⟩ ⟩ (p , String)) since it)
--             ≅ (Lift (BaseExprᵘ p String) since isSetoid:byDiscrete)
--     rep' = f since P
--       where
--         f : (isCategory.Hom (_:&_.of fst ⟨ BaseExprInfer ⟩) (p , ⊤-𝒰)
--                     (⟨ snd ⟨ BaseExprInfer ⟩ ⟩ (p , String)) since it)

--                     ⟶ (Lift (BaseExprᵘ p String) since isSetoid:byDiscrete)
--         f = (λ (_ , x) → ↥ (x tt)) since {!!}

--         g : (Lift (BaseExprᵘ p String) since isSetoid:byDiscrete)
--             ⟶
--             (isCategory.Hom (_:&_.of fst ⟨ BaseExprInfer ⟩) (p , ⊤-𝒰)
--                     (⟨ snd ⟨ BaseExprInfer ⟩ ⟩ (p , String)) since it)

--         g = (λ x → refl , (λ x₁ → lower x)) since {!!}

--         P = record { inverse-◆ = g ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }



{-
    Sᵘ : ⟨ ℰ ⟩ -> ⟨ ℰ ⟩
    Sᵘ (a , a⃨) = a , (⟨ ⟨ T ⟩ a ⟩ a⃨)

    macro S = #structureOn Sᵘ

    map-S : ∀{a b} -> a ⟶ b -> S a ⟶ S b
    map-S {a , a⃨} {b , b⃨} (f , f⃨) = f , g⃨
      where
        -- g : base (S a) ⟶ base (S b)
        -- g = f

        g⃨ : ⟨ ⟨ T ⟩ a ⟩ a⃨ ⟶ ⟨ ⟨ T ⟩ b ⟩ b⃨
        g⃨ = ((↳ ⟨ T ⟩ a) ⇂ f⃨) ◆ ⟨ ⟨ T ⇂ f ⟩ ⟩ b⃨

    instance
      isSetoidHom:map-S : ∀{a} {b} -> isSetoidHom (a ⟶ b) (S a ⟶ S b) (map-S)
      isSetoidHom.cong-∼ (isSetoidHom:map-S {a , a⃨} {b , b⃨}) {f , f⃨} {g , g⃨} (p , p⃨) = p , q
        where
          p' : f⃨ ∼ g⃨
          p' = unit-r-◆ ⁻¹ ∙ p⃨

          q : ((↳ ⟨ T ⟩ a) ⇂ f⃨ ◆ ⟨ ⟨ T ⇂ f ⟩ ⟩ b⃨) ◆ id
              ∼
              (↳ ⟨ T ⟩ a) ⇂ g⃨ ◆ ⟨ ⟨ T ⇂ g ⟩ ⟩ b⃨
          q = unit-r-◆ ∙ ((↳ ⟨ T ⟩ a) ⇂≀ p') ◈ ⟨ ⟨ T ⇂≀ p ⟩ ⟩ b⃨

    functoriality-id-S : ∀{a} -> map-S (idOn a) ∼ idOn (S a)
    functoriality-id-S {a , a⃨} = refl , ((functoriality-id {{of ↳ ⟨ T ⟩ a}} ◈ ⟨ ⟨ functoriality-id ⟩ ⟩ a⃨ ∙ unit-2-◆) ◈ refl ∙ unit-r-◆)

    functoriality-◆-S : ∀{a b c : ⟨ ℰ ⟩} -> {f : a ⟶ b} {g : b ⟶ c} -> map-S (f ◆ g) ∼ map-S f ◆ map-S g
    functoriality-◆-S {a , a⃨} {b , b⃨} {c , c⃨} {f , f⃨} {g , g⃨} = refl , (({!?!} ∙ assoc-l-◆) ◈ refl ∙ unit-r-◆)


    instance
      isFunctor:S : isFunctor ℰ ℰ S
      isFunctor.map isFunctor:S = map-S
      isFunctor.isSetoidHom:map isFunctor:S = isSetoidHom:map-S
      isFunctor.functoriality-id isFunctor:S = functoriality-id-S
      isFunctor.functoriality-◆ isFunctor:S = {!!}

-}
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


-}
