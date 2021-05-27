

module Verification.Core.Category.Limit.Kan.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Iso
open import Verification.Core.Category.Functor.Adjunction
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Lift
open import Verification.Core.Category.Limit.Kan.Terminal
open import Verification.Core.Homotopy.Level
open import Verification.Core.Algebra.Basic.Monoid
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.Instance.Level
open import Verification.Core.Order.Instance.Product

--------------------------------------------------------------------
-- === Definition via kan extensions
-- mostly from nlab (https://ncatlab.org/nlab/show/Kan+extension)


private
  Fun[_,_] = Category:Functor

  infixl 70 _◇_
  _◇_ = comp-Cat

--------------------------------------------------------------------
-- Pullback functor

module _ {𝒞 : Category 𝑖} {𝒞' : Category 𝑗} where

  infixl 60 _*

  _* : ∀{𝒟 : Category 𝑘} -> (p : Functor 𝒞 𝒞') -> Functor Fun[ 𝒞' , 𝒟 ] Fun[ 𝒞 , 𝒟 ]
  ⟨ p * ⟩ F = p ◇ F
  IFunctor.map (of (p *)) α = [ p ]◆-H α
  IFunctor.functoriality-id (of (p *)) = {!!}
  IFunctor.functoriality-◆ (of (p *)) = {!!}
  IFunctor.functoriality-≣ (of (p *)) = {!!}

  -- isRightKanExtension : ∀{𝒟 : Category 𝑘} -> (p : Functor 𝒞 𝒞') -> (G : Functor Fun[ 𝒞 , 𝒟 ] Fun[ 𝒞' , 𝒟 ]) -> 𝒰 _
  -- isRightKanExtension p G = p * ⊣ G

  -- hasGlobalRan : ∀(𝒟 : Category 𝑘) -> (p : Functor 𝒞 𝒞') -> 𝒰 _
  -- hasGlobalRan 𝒟 p = ∑ λ (G : Functor Fun[ 𝒞 , 𝒟 ] Fun[ 𝒞' , 𝒟 ]) -> isRightKanExtension p G

  hasGlobalRan : ∀(𝒟 : Category 𝑘) -> (p : Functor 𝒞 𝒞') -> 𝒰 _
  hasGlobalRan 𝒟 p = hasRightAdjoint (F)
    where F : Functor Fun[ 𝒞' , 𝒟 ] Fun[ 𝒞 , 𝒟 ]
          F = p *

  hasGlobalLan : ∀(𝒟 : Category 𝑘) -> (p : Functor 𝒞 𝒞') -> 𝒰 _
  hasGlobalLan 𝒟 p = hasLeftAdjoint (F)
    where F : Functor Fun[ 𝒞' , 𝒟 ] Fun[ 𝒞 , 𝒟 ]
          F = p *










-- ↑_ = Lift

-- instance ICategory:𝟙 = #openstruct Category:𝟙




-- !-Cat : ∀(𝒞 : Category 𝑖) -> Functor 𝒞 Category:𝟙
-- ⟨ !-Cat 𝒞 ⟩ z = ₀
-- IFunctor.map (of !-Cat 𝒞) x = id
-- IFunctor.functoriality-id (of !-Cat 𝒞) = refl
-- IFunctor.functoriality-◆ (of !-Cat 𝒞) = refl
-- IFunctor.functoriality-≣ (of !-Cat 𝒞) x = refl

-- instance IFunctor:!-Cat = #openstruct !-Cat

-- instance
--   Index-Notation:Hom : ∀{C : 𝒰 𝑖} {{ICategory:C : ICategory C 𝑗}} -> {b : C} -> Index-Notation (∀{a : C} -> Hom a b) (C) IAnything (λ (H , a) -> Hom a b)
--   (Index-Notation:Hom Index-Notation.⌄ x) i = x {i}

has_ShapedLimits : (S : Category 𝑗) (𝒞 : Category 𝑗) -> 𝒰 _
has_ShapedLimits S 𝒞 = hasGlobalRan 𝒞 (! S)

-- lim : {𝒟 : Category 𝑖} {𝒞 : Category 𝑖} {{limits : has(𝒟)ShapedLimits 𝒞}} -> (F : 𝒟 ⟶ 𝒞) -> ⟨ 𝒞 ⟩
-- lim {{limits}} F = ⟨ ⟨ ⟨ limits ⟩ ⟩ F ⟩ (↥ tt)

lim : {𝒟 : Category 𝑖} {𝒞 : Category 𝑖} {{limits : has(𝒟)ShapedLimits 𝒞}} -> (F : 𝒟 ⟶ 𝒞) -> ⟨ 𝒞 ⟩
lim {{limits}} F = ⟨ ⟨ ⟨ limits ⟩ ⟩ F ⟩ (↥ tt)

has_ShapedColimits : (S : Category 𝑗) (𝒞 : Category 𝑗) -> 𝒰 _
has_ShapedColimits S 𝒞 = hasGlobalLan 𝒞 (! S)

colim-D : {𝒟 : Category 𝑖} {𝒞 : Category 𝑖} {{limits : has(𝒟)ShapedColimits 𝒞}} -> (F : 𝒟 ⟶ 𝒞) -> 𝟙 ⟶ 𝒞
colim-D {{limits}} F = ⟨ ⟨ limits ⟩ ⟩ F

colim : {𝒟 : Category 𝑖} {𝒞 : Category 𝑖} {{limits : has(𝒟)ShapedColimits 𝒞}} -> (F : 𝒟 ⟶ 𝒞) -> ⟨ 𝒞 ⟩
colim {{limits}} F = ⟨ ⟨ ⟨ limits ⟩ ⟩ F ⟩ (↥ tt)





-- has_ShapedLimits : (S : Category 𝑖) (𝒞 : Category 𝑗) -> 𝒰 _
-- has_ShapedLimits S 𝒞 = hasGlobalRan 𝒞 (!-Cat S)

------------------
-- 𝒰 has products

Functor:lower : ∀{X : Category 𝑖} {𝑗} -> Functor (Category:Lift {𝑗 = 𝑗} X) X
⟨ Functor:lower ⟩ (↥ x) = x
IFunctor.map (of Functor:lower) (↥ f) = f
IFunctor.functoriality-id (of Functor:lower) = refl
IFunctor.functoriality-◆ (of Functor:lower) = refl
IFunctor.functoriality-≣ (of Functor:lower) (↥ p) = p

free-Diagram : ∀{X : Category 𝑖} {Q : Quiver 𝑗} -> (f : QuiverHom Q (ForgetCategory X)) -> Functor ((Category:Free Q)) X
free-Diagram {X = X} f =
  let f1 = (map-Category:Free f) ◇ (eval-Category:Free)
  in f1

_ᵒᵖ-Q : Quiver 𝑖 -> Quiver 𝑖
⟨ Q ᵒᵖ-Q ⟩ = ⟨ Q ⟩
IQuiver.Edge (of (Q ᵒᵖ-Q)) a b = Edge b a
IQuiver._≈_ (of (Q ᵒᵖ-Q)) = _≈_
IQuiver.isEquivRelInst (of (Q ᵒᵖ-Q)) = isEquivRelInst

-- free-Diagramᵒᵖ : ∀{X : Category 𝑖} {Q : Quiver 𝑗} -> (f : QuiverHom (Q ᵒᵖ-Q) (ForgetCategory X)) -> Functor ((Category:Free Q) ᵒᵖ) X
-- ⟨ free-Diagramᵒᵖ f ⟩ x = ⟨ f ⟩ x
-- IFunctor.map (of free-Diagramᵒᵖ {X = X} {Q = Q} f) {a} {b} e =
--   let XX = map-Category:Free f
--       e2 = map {{of XX}} {!!}
--   in {!!}
-- IFunctor.functoriality-id (of free-Diagramᵒᵖ f) = {!!}
-- IFunctor.functoriality-◆ (of free-Diagramᵒᵖ f) = {!!}
-- IFunctor.functoriality-≣ (of free-Diagramᵒᵖ f) = {!!}


free-Diagram-Lift : ∀{X : Category 𝑖} {Q : Quiver ⊥} -> (f : QuiverHom Q (ForgetCategory X)) -> (↑ Category:Free Q) ⟶ X
free-Diagram-Lift {X = X} f =
  let f1 = Functor:lower ◇ (map-Category:Free f) ◇ (eval-Category:Free)
  in f1





{-
module _ {𝒞 : Category 𝑗} where
  private
    instance _ = of 𝒞

    f : Functor Category:𝟙 𝒞 -> ⟨ 𝒞 ⟩
    f F = ⟨ F ⟩ tt

    g : ⟨ 𝒞 ⟩ -> Functor Category:𝟙 𝒞
    ⟨ g x ⟩ _ = x
    IFunctor.map (of g x) id-Q = id
    IFunctor.map (of g x) (some (last ()))
    IFunctor.map (of g x) (some (() ∷ p))
    IFunctor.functoriality-id (of g x) = refl
    IFunctor.functoriality-◆ (of g x) {a} {.a} {.a} {id-Q} {id-Q} = sym unit-2-◆
    IFunctor.functoriality-◆ (of g x) {a} {.a} {c} {id-Q} {some (() ∷ e)}
    IFunctor.functoriality-◆ (of g x) {a} {b} {c} {some (last ())} {w}
    IFunctor.functoriality-◆ (of g x) {a} {b} {c} {some (() ∷ v)} {w}
    IFunctor.functoriality-≣ (of g x) {f = id-Q} {g = id-Q} e = refl
    IFunctor.functoriality-≣ (of g x) {f = some (last ())} {g = some w} (some e)
    IFunctor.functoriality-≣ (of g x) {f = some (() ∷ v)} {g = some w} (some e)

    fg : ∀(x) -> f (g x) ≡ x
    fg x = refl
-}

    -- gf : ∀(F) -> (g (f F)) ≣ F
    -- gf (⌘ F) = {!!}

  -- instance
  --   Abstract-Obj : Abstract ⟨ 𝒞 ⟩ (Functor Category:𝟙 𝒞)
  --   Abstract-Obj = {!!}


module _ {Q : Quiver 𝑖} {𝒟 : Category 𝑗} {F G : Functor (Category:Free Q) 𝒟} where
  module _ (α : ∀ (x : ⟨ Q ⟩) -> ⟨ F ⟩ x ⟶ ⟨ G ⟩ x) (αp : ∀{a b : ⟨ Q ⟩} -> ∀(e : Edge {{of Q}} a b) -> α a ◆ map (⩚ e) ≣ map (⩚ e) ◆ α b) where
    private
      instance _ = of 𝒟
      P₀ : ∀{a b : ⟨ Q ⟩} -> ∀(e : QPath {{of Q}} a b) -> α a ◆ map (⩚ e) ≣ map (⩚ e) ◆ α b
      P₀ (last e) = αp e
      P₀ {a = a} {b} (e ∷ es) =
        (refl ◈ functoriality-◆ {f = ⩚ e} {g = ⩚ es})
        ∙ assoc-r-◆
        ∙ (αp e ◈ refl)
        ∙ assoc-l-◆
        ∙ (refl ◈ P₀ es)
        ∙ assoc-r-◆
        ∙ (functoriality-◆ ⁻¹ ◈ refl)

      P₁ : ∀{a b : ⟨ Q ⟩} -> ∀(e : Hom {{of (Category:Free Q)}} a b) -> α a ◆ map (⩚ e) ≣ map (⩚ e) ◆ α b
      P₁ id-Q = (refl ◈ functoriality-id) ∙ unit-r-◆
                                          ∙ unit-l-◆ ⁻¹
                                          ∙ (functoriality-id ⁻¹ ◈ refl)
      P₁ (some es) = P₀ es

    free-Diagram-Natimpl :  Natural F G
    ⟨ free-Diagram-Natimpl ⟩ {x} = α x
    INatural.naturality (of free-Diagram-Natimpl) {x} {y} f = P₁ f


module _ {Q : Quiver ⊥} {𝒟 : Category 𝑗} {F G : ↑ (Category:Free Q) ⟶ 𝒟} where
  module _ (α : ∀ (x : ⟨ Q ⟩) -> ⟨ F ⟩ (↥ x) ⟶ ⟨ G ⟩ (↥ x)) (αp : ∀{a b : ⟨ Q ⟩} -> ∀(e : Edge {{of Q}} a b) -> α a ◆ map ((⩚ e)) ≣ map ((⩚ e)) ◆ α b) where
    free-Diagram-Nat :  Natural (F) (G)
    ⟨ free-Diagram-Nat ⟩ {↥ x} = α x
    of free-Diagram-Nat = {!!}


--------------------------------------------------------------------
-- Cones

module _ {𝒞 : Category 𝑖} where
  Diagram-𝟙 : (x : ⟨ 𝒞 ⟩) -> 𝟙 ⟶ 𝒞
  Diagram-𝟙 x = free-Diagram-Lift D
    where D : QuiverHom ` 𝟙-𝒰 ` (ForgetCategory 𝒞)
          ⟨ D ⟩ _ = x
          IQuiverHom.qmap (of D) ()

  Cone : {𝒟 : Category 𝑖} (D : 𝒟 ⟶ 𝒞) -> ⟨ 𝒞 ⟩ -> 𝒰 𝑖
  Cone {𝒟 = 𝒟} D x = ⟨ ! 𝒟 * ⟩ (Diagram-𝟙 x) ⟶ D

  instance
    Cast:Diagram-𝟙 : Cast ⟨ 𝒞 ⟩ IAnything (𝟙 ⟶ 𝒞)
    Cast.cast Cast:Diagram-𝟙 a = Diagram-𝟙 a

