
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Quiver where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Iso

-- == Free categories
-- | Given a graph, we can define a /free/ category on this graph.
--   In order to do this, we need to define graphs first, which, in order to stress that
--   they are possibly non-simple and also allowed to be multi-graphs, we are going to call /quivers/.

-- | Since we want the quivers to be as compatible with our definition of categories as possible,
--   we also equip them with an equivalence relation on the edges.

-- [Definition]
-- A type |X| is a quiver,
record IQuiver (X : 𝒰 𝑖) (𝑗 : 𝔏 ^ 2) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  -- |> if the following data is given:
  field Edge : X -> X -> 𝒰 (𝑗 ⌄ 0)
        _≈_ : ∀{a b : X} -> (f g : Edge a b) -> 𝒰 (𝑗 ⌄ 1)
        {{isEquivRelInst}} : ∀{a b : X} -> isEquivRel (_≈_ {a = a} {b = b})
-- //

open IQuiver {{...}} public
unquoteDecl Quiver quiver = #struct "Qvr" (quote IQuiver) "X" Quiver quiver

-- [Definition]
-- | A homomorphism of quivers is a function which maps vertices and edges.
record IQuiverHom (X : Quiver 𝑖) (Y : Quiver 𝑗) (f : ⟨ X ⟩ -> ⟨ Y ⟩) : 𝒰 (𝑖 ､ 𝑗) where
  field qmap : ∀{a b : ⟨ X ⟩} -> Edge a b -> Edge (f a) (f b)
-- //

open IQuiverHom {{...}} public
unquoteDecl QuiverHom quiverHom = #struct "QvrHom" (quote IQuiverHom) "f" QuiverHom quiverHom


-- [Definition]
-- | The category of quivers is given by:
module _ {X : Quiver 𝑖} {Y : Quiver 𝑗} {Z : Quiver 𝑘} where
  comp-Quiver : QuiverHom X Y -> QuiverHom Y Z -> QuiverHom X Z
  ⟨ comp-Quiver f g ⟩ = comp-𝒰 ⟨ f ⟩ ⟨ g ⟩
  IQuiverHom.qmap (of (comp-Quiver f g)) e = qmap (qmap e)


Category:Quiver : (𝑖 : 𝔏 ^ 3) -> Category (⨆ 𝑖 ⁺ , ⨆ 𝑖 , ⨆ 𝑖)
⟨ Category:Quiver 𝑖 ⟩ = Quiver 𝑖
isCategory.Hom (of Category:Quiver 𝑖) = QuiverHom
isCategory._≣_ (of Category:Quiver 𝑖) f g = {!!}
isCategory.isEquivRel:≣ (of Category:Quiver 𝑖) = {!!}
⟨ isCategory.id (of Category:Quiver 𝑖) ⟩ = id
IQuiverHom.qmap (of (isCategory.id (of Category:Quiver 𝑖))) = id
isCategory._◆_ (of Category:Quiver 𝑖) = comp-Quiver
isCategory._◈_ (of Category:Quiver 𝑖) = {!!}
isCategory.unit-l-◆ (of Category:Quiver 𝑖) = {!!}
isCategory.unit-r-◆ (of Category:Quiver 𝑖) = {!!}
isCategory.unit-2-◆ (of Category:Quiver 𝑖) = {!!}
isCategory.assoc-l-◆ (of Category:Quiver 𝑖) = {!!}
isCategory.assoc-r-◆ (of Category:Quiver 𝑖) = {!!}
-- //

instance isCategory:Quiver = #openstruct Category:Quiver



-- [Lemma]
-- | There is a functor from |Category ⟶ Quiver|.
ForgetCategory : Category 𝑖 -> Quiver 𝑖
⟨ ForgetCategory X ⟩ = ⟨ X ⟩
IQuiver.Edge (of (ForgetCategory X)) = Hom
IQuiver._≈_ (of (ForgetCategory X)) = _≣_
IQuiver.isEquivRelInst (of (ForgetCategory X)) = isEquivRel:≣

Category:Forget = ForgetCategory


map-ForgetCategory : ∀{X Y : Category 𝑖} -> (f : X ⟶ Y) -> (ForgetCategory X) ⟶ (ForgetCategory Y)
⟨ map-ForgetCategory f ⟩ = ⟨ f ⟩
IQuiverHom.qmap (of (map-ForgetCategory f)) = map

instance
  IFunctor:ForgetCategory : IFunctor (′ Category 𝑖 ′) (′ Quiver 𝑖 ′) ForgetCategory
  IFunctor.map IFunctor:ForgetCategory = map-ForgetCategory
  IFunctor.functoriality-id IFunctor:ForgetCategory = {!!}
  IFunctor.functoriality-◆ IFunctor:ForgetCategory = {!!}
  IFunctor.functoriality-≣ IFunctor:ForgetCategory = {!!}

Functor:ForgetCategory : Functor (′ (Category 𝑖) ′) (′ Quiver 𝑖 ′)
Functor:ForgetCategory = functor ForgetCategory
-- //



{-
Quiver:LiftQuiver : (Q : Quiver 𝑖) -> ∀{𝑗} -> Quiver (zipL 𝑖 𝑗)
⟨ Quiver:LiftQuiver Q {𝑗 = J} ⟩ = Lift {j = J ⌄ 0} ⟨ Q ⟩
IQuiver.Edge (of (Quiver:LiftQuiver Q {𝑗 = J})) (lift a) (lift b) = Lift {j = J ⌄ ₁} (Edge a b)
IQuiver._≈_ (of (Quiver:LiftQuiver Q {𝑗 = J})) = {!!}
IQuiver.isEquivRelInst (of (Quiver:LiftQuiver Q {𝑗 = J})) = {!!}


instance
  ILiftHom:QuiverHom : ∀{C : Quiver 𝑖} {D : Quiver 𝑗} -> ILiftHom (Quiver:LiftQuiver C {𝑗}) (Quiver:LiftQuiver D {𝑖}) (QuiverHom C D)
  ⟨ ⟨ ILiftHom.liftHom ILiftHom:QuiverHom ⟩ F ⟩ x = {!!}
  of (⟨ ILiftHom.liftHom ILiftHom:QuiverHom ⟩ F) = {!!}
  of (ILiftHom.liftHom ILiftHom:QuiverHom) = {!!}

instance
  ILiftHom:QuiverHomForget : ∀{C : Quiver 𝑖} {D : Category 𝑗} -> ILiftHom (Quiver:LiftQuiver C {joinL 𝑖 𝑗}) (ForgetCategory (Category:LiftCategory D {joinL 𝑖 𝑗})) (QuiverHom C (ForgetCategory D))
  ⟨ ⟨ ILiftHom.liftHom ILiftHom:QuiverHomForget ⟩ F ⟩ (lift x) = lift (⟨ F ⟩ x)
  of (⟨ ILiftHom.liftHom ILiftHom:QuiverHomForget ⟩ F) = {!!}
  of (ILiftHom.liftHom ILiftHom:QuiverHomForget) = {!!}

-}

