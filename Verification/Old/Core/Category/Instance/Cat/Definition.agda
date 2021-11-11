

module Verification.Old.Core.Category.Instance.Cat.Definition where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type.Definition
open import Verification.Old.Core.Category.Iso

------------------
-- The category of categories


id-Cat : ∀{X : Category 𝑖} -> Functor X X
⟨ id-Cat ⟩ = id-𝒰
IFunctor.map (of id-Cat) f = f
IFunctor.functoriality-id (of id-Cat) = refl
IFunctor.functoriality-◆ (of id-Cat) = refl
IFunctor.functoriality-≣ (of id-Cat) = id


comp-Cat : {X : Category 𝑖} {Y : Category 𝑗} {Z : Category 𝑘} -> (F : Functor X Y) -> (G : Functor Y Z) -> Functor X Z
⟨ comp-Cat F G ⟩ = comp-𝒰 ⟨ F ⟩ ⟨ G ⟩
IFunctor.map (of comp-Cat F G) f = map (map f)
IFunctor.functoriality-id (of comp-Cat F G) = {!!}
IFunctor.functoriality-◆ (of comp-Cat F G) = {!!}
IFunctor.functoriality-≣ (of comp-Cat F G) = {!!}

-- instance IFunctor:comp-Cat = #openstruct comp-Cat


-- IFunctor:comp-Cat : {X : Category 𝑖} {Y : Category 𝑗} {Z : Category 𝑘}
--                     -> (F : Functor X Y) -> (G : Functor Y Z) -> IFunctor X Z (comp-Cat ⟨ F ⟩ ⟨ G ⟩)
-- IFunctor.map (IFunctor:comp-Cat F G) f = map (map f)
--   -- ≡[ i ]⟨ map (functoriality-id) ⟩
-- IFunctor.functoriality-id (IFunctor:comp-Cat F G) {a = a} =  map (map id)   ≣⟨ functoriality-≣ functoriality-id ⟩
--                                                              map id         ≣⟨ functoriality-id ⟩
--                                                              id ∎
--  -- a [ i ]⟨ map (functoriality-◆ f g i) ⟩
--  -- (map f) (map g) ⟩
-- IFunctor.functoriality-◆ (IFunctor:comp-Cat F G) {f = f} {g} = map (map (f ◆ g)) ≣⟨ functoriality-≣ functoriality-◆ ⟩
--                                                                map (map f ◆ map g) ≣⟨ functoriality-◆ ⟩
--                                                                map (map f) ◆ map (map g) ∎
-- IFunctor.functoriality-≣ (IFunctor:comp-Cat F G) {f = f} {g} x = functoriality-≣ (functoriality-≣ x)

-- Functor:comp-Cat : {X : Category 𝑖} {Y : Category 𝑗} {Z : Category 𝑘}
--                     -> (F : Functor X Y) -> (G : Functor Y Z) -> Functor X Z
-- Functor:comp-Cat F G = functor _ {{IFunctor:comp-Cat F G}}

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record ≣-Functor (F G : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field
      object-path : ⟨ F ⟩ ≡ ⟨ G ⟩
      arrow-path  : ∀{a b} -> ∀(f : Hom a b) -> transport (λ i -> Hom (object-path i a) (object-path i b)) (map f) ≣ map f



Category:Category : (𝑖 : 𝔏 ^ 3) -> Category _
⟨ Category:Category 𝑖 ⟩ = Category 𝑖
isCategory.Hom (of Category:Category 𝑖) = Functor
isCategory._≣_ (of Category:Category 𝑖) = ≣-Functor
isCategory.isEquivRel:≣ (of Category:Category 𝑖) = {!!}
isCategory.id (of Category:Category 𝑖) = id-Cat
isCategory._◆_ (of Category:Category 𝑖) = comp-Cat
isCategory.unit-l-◆ (of Category:Category 𝑖) = {!!}
isCategory.unit-r-◆ (of Category:Category 𝑖) = {!!}
isCategory.unit-2-◆ (of Category:Category 𝑖) = {!!}
isCategory.assoc-l-◆ (of Category:Category 𝑖) = {!!}
isCategory.assoc-r-◆ (of Category:Category 𝑖) = {!!}
isCategory._◈_ (of Category:Category 𝑖) = {!!}

instance isCategory:Category = #openstruct Category:Category

-- instance
--   isCategory:Category : isCategory (Category 𝑖) _
--   isCategory.Hom isCategory:Category = Functor
--   isCategory._≣_ isCategory:Category F G = ∑ λ (p : ⟨ F ⟩ ≡ ⟨ G ⟩) -> ∀{a b} -> ∀(f : Hom a b) -> PathP (λ i -> Hom (p i a) (p i b)) (map f) (map f)
--   isCategory.isEquivRel:≣ isCategory:Category = {!!}
--   isCategory.id isCategory:Category = Functor:id-Cat
--   isCategory._◆_ isCategory:Category = Functor:comp-Cat
--   isCategory._◈_ isCategory:Category = {!!}
--   isCategory.unit-l-◆ isCategory:Category = {!!}
--   isCategory.unit-r-◆ isCategory:Category = {!!}
--   isCategory.unit-2-◆ isCategory:Category = {!!}
--   isCategory.assoc-l-◆ isCategory:Category = {!!}
--   isCategory.assoc-r-◆ isCategory:Category = {!!}


{-

LiftCategory : Category 𝑖 -> (J : ULevel ^ 3) -> 𝒰 (J ⌄ ₀ ⊔ 𝑖 ⌄ ₀)
LiftCategory X J = Lift {j = J ⌄ ₀} ⟨ X ⟩

instance
  isCategory:LiftCategory : ∀{C : Category 𝑖} -> isCategory (LiftCategory C 𝑗) _
  isCategory.Hom (isCategory:LiftCategory {𝑗 = J} {C = C}) (lift a) (lift b) = Lift {j = J ⌄ ₁} (Hom a b)
  isCategory._≣_ (isCategory:LiftCategory {𝑗 = J} {C = C}) (lift f) (lift g) = Lift {j = J ⌄ ₂} (f ≣ g)
  isCategory.isEquivRel:≣ (isCategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  isCategory.id (isCategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  isCategory._◆_ (isCategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  isCategory._◈_ (isCategory:LiftCategory {𝑗 = J} {C = C}) = {!!}
  isCategory.unit-l-◆ (isCategory:LiftCategory {C}) = {!!}
  isCategory.unit-r-◆ (isCategory:LiftCategory {C}) = {!!}
  isCategory.unit-2-◆ (isCategory:LiftCategory {C}) = {!!}
  isCategory.assoc-l-◆ (isCategory:LiftCategory {C}) = {!!}
  isCategory.assoc-r-◆ (isCategory:LiftCategory {C}) = {!!}


Category:LiftCategory : ∀(C : Category 𝑖) {𝑗 : ULevel ^ 3} -> Category (𝑖 ⌄ ₀ ⊔ 𝑗 ⌄ ₀ , 𝑖 ⌄ ₁ ⊔ 𝑗 ⌄ ₁ , 𝑖 ⌄ ₂ ⊔ 𝑗 ⌄ ₂)
Category:LiftCategory C {j} = category (LiftCategory C j) {{isCategory:LiftCategory {𝑗 = j} {C = C}}}


instance
  ILiftHom:Functor : ∀{C : Category 𝑖} {D : Category 𝑗} -> ILiftHom (Category:LiftCategory C {zipL 𝑖 𝑗}) (Category:LiftCategory D {zipL 𝑖 𝑗}) (Functor C D)
  ⟨ ⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F ⟩ (lift x) = lift (⟨ F ⟩ x)
  IFunctor.map (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) (lift f) = lift (map f)
  IFunctor.functoriality-id (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) = {!!}
  IFunctor.functoriality-◆ (of (⟨ ILiftHom.liftHom ILiftHom:Functor ⟩ F)) = {!!}
  ⟨ IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G ⟩ x = lower (⟨ G ⟩ (lift x))
  IFunctor.map (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) f = lower (map (lift f))
  IFunctor.functoriality-id (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) = {!!}
  IFunctor.functoriality-◆ (of (IIso-𝒰.inverse (of (ILiftHom.liftHom ILiftHom:Functor)) G)) = {!!}
  IIso-𝒰./⟲ (of (ILiftHom.liftHom ILiftHom:Functor)) = {!!}
  IIso-𝒰./⟳ (of (ILiftHom.liftHom ILiftHom:Functor)) = {!!}


-}
