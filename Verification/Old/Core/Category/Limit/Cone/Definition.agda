{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Limit.Definition where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Adjunction


--------------------------------------------------------------------
-- === Definition via cones


Diagram : (S : SmallCategory) (X : Category 𝑖) -> 𝒰 _
Diagram S X = Functor S X



-- instance
IFunctor:∆ : ∀{X : Category 𝑖} {Y : Category 𝑗} -> {y : ⟨ Y ⟩} -> IFunctor X Y (∆ {A = ⟨ X ⟩} y)
IFunctor.map IFunctor:∆ _ = id
IFunctor.functoriality-id IFunctor:∆ = refl
IFunctor.functoriality-◆ IFunctor:∆ = sym (unit-2-◆)
IFunctor.functoriality-≣ IFunctor:∆ x = {!!}

-- Functor:∆ : ∀{X : 𝒰 𝑖} {{_ : ICategory X 𝑗}} {Y : 𝒰 𝑗} {{_ : ICategory Y 𝑗𝑗}} -> (y : Y) -> Functor (category X) (category Y)
-- Functor:∆ y = functor (∆ y) {{IFunctor:∆}}

Functor:∆ : ∀{X : Category 𝑖} {Y : Category 𝑗} -> (y : ⟨ Y ⟩) -> Functor X Y
Functor:∆ y = functor (∆ y) {{IFunctor:∆}}


record ICone {S : SmallCategory} {X : Category 𝑖} (d : Diagram S X) (x : ⟨ X ⟩) : 𝒰 (𝑖 ⌄ 1 ､ 𝑖 ⌄ 2) where
  field ▲ : ∀{s : ⟨ S ⟩} -> Hom x (⟨ d ⟩ s)
        {{Natural:▲}} : INatural (Functor:∆ x) d ▲
  ▲[_] : (s : ⟨ S ⟩) -> Hom x (⟨ d ⟩ s)
  ▲[_] s = ▲ {s = s}
open ICone {{...}} public
unquoteDecl Cone cone = #struct "Cone" (quote ICone) "x" Cone cone


record IConeHom {S} {X : Category 𝑖} {d : Diagram S X} (x y : Cone d) (f : Hom ⟨ x ⟩ ⟨ y ⟩) : 𝒰 (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 2) where
  field ▲/ : ∀{s : ⟨ S ⟩} -> f ◆ ▲[ s ] ≣ ▲[ s ]
open IConeHom {{...}} public


unquoteDecl ConeHom coneHom = #struct "ConeHom" (quote IConeHom) "f" ConeHom coneHom


id-ConeHom : ∀{S} {X : Category 𝑖} {d : Diagram S X} {x : Cone d} -> ConeHom x x
⟨ id-ConeHom ⟩ = id
IConeHom.▲/ (of id-ConeHom) = unit-l-◆


comp-ConeHom : ∀{S} {X : Category 𝑖} {d : Diagram S X} {x y z : Cone d} (f : ConeHom x y) (g : ConeHom y z) -> ConeHom x z
⟨ comp-ConeHom f g ⟩ = ⟨ f ⟩ ◆ ⟨ g ⟩
IConeHom.▲/ (of (comp-ConeHom f g)) {s = s} = (⟨ f ⟩ ◆ ⟨ g ⟩) ◆ ▲[ s ] ≣⟨ assoc-l-◆ ⟩
                                                          ⟨ f ⟩ ◆ (⟨ g ⟩ ◆ ▲[ s ]) ≣⟨ refl ◈ ▲/ ⟩
                                                          ⟨ f ⟩ ◆ ▲[ s ]          ≣⟨ ▲/ ⟩
                                                          ▲[ s ]                 ∎


instance
  ICategory:Cone : ∀{S} {X : Category 𝑖} {D : Diagram S X} -> ICategory (Cone D) (⨆ 𝑖 , 𝑖 ⌄ 2)
  ICategory.Hom ICategory:Cone = ConeHom
  ICategory._≣_ ICategory:Cone f g = ⟨ f ⟩ ≣ ⟨ g ⟩
  IEquiv.refl (ICategory.IEquiv:≣ (ICategory:Cone {X = X})) = refl
  IEquiv.sym (ICategory.IEquiv:≣ (ICategory:Cone {X = X})) = sym
  IEquiv._∙_ (ICategory.IEquiv:≣ (ICategory:Cone {X = X})) = _∙_
  ICategory.id ICategory:Cone = id-ConeHom
  ICategory._◆_ ICategory:Cone = comp-ConeHom
  ICategory._◈_ (ICategory:Cone {X = X}) p q = _◈_ {{of X}} p q
  ICategory.unit-l-◆ (ICategory:Cone {X = X}) = unit-l-◆ {{of X}}
  ICategory.unit-r-◆ (ICategory:Cone {X = X}) = unit-r-◆ {{of X}}
  ICategory.unit-2-◆ (ICategory:Cone {X = X}) = unit-2-◆ {{of X}}
  ICategory.assoc-l-◆ (ICategory:Cone {X = X}) = assoc-l-◆ {{of X}}
  ICategory.assoc-r-◆ (ICategory:Cone {X = X}) = assoc-r-◆ {{of X}}


-- ICategory:Cone : ∀{S} {X : Category 𝑖} {D : Diagram S X} -> ICategory (Cone D) (⨆ 𝑖 , 𝑖 ⌄ ₂)
-- ICategory.ICategoryInst ICategory:Cone = ICategory:Cone

Category:Cone : ∀{S} {X : Category 𝑖} (D : Diagram S X) -> Category (⨆ 𝑖 , ⨆ 𝑖 , 𝑖 ⌄ 2)
Category:Cone {𝑖 = 𝑖} {X = X} D = category (Cone D) {{ICategory:Cone {𝑖 = 𝑖} {X = X} {D = D}}}




record ITerminal (X : Category 𝑖) (x : ⟨ X ⟩) : 𝒰 (⨆ 𝑖 ⁺) where
  field ! : ∀{a : ⟨ X ⟩} -> Hom a x
        unique : ∀{a : ⟨ X ⟩} -> (f : Hom a x) -> f ≣ !
open ITerminal {{...}} public
unquoteDecl Terminal terminal = #struct "Term" (quote ITerminal) "x" Terminal terminal

ILimit : ∀{S} {X : Category 𝑖} -> (D : Diagram S X) -> (x : Cone D) -> 𝒰 _
ILimit D x = ITerminal (Category:Cone D) x

Limit : ∀{S} {X : Category 𝑖} -> (D : Diagram S X) -> 𝒰 _
Limit D = Terminal (Category:Cone D)

Colimit : ∀{S} {X : Category 𝑖} -> (D : Diagram S X) -> 𝒰 _
Colimit D = Terminal (Category:Cone D)

record has_ShapedLimits (S : SmallCategory) (X : 𝒰 𝑖) {𝑗} {{_ : ICategory X 𝑗}} : 𝒰 (𝑖 ⁺ ⊔ ⨆ 𝑗 ⁺) where
  field lim : (D : Diagram S (category X)) -> Limit D
open has_ShapedLimits {{...}} public



-- record ICategory⍮With_ShapedLimits (S : 𝒰₀) {{_ : ISmallCategory S}} (X : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ⁺ ⊔ ⨆ 𝑗 ⁺) where
--   field {{CategoryInstance}} : ICategory X 𝑗
--         lim : (D : Diagram (category S) (category X)) -> Limit D
-- open ICategory⍮With_ShapedLimits {{...}} public

-- record ICategory⍮With_ShapedColimits (S : 𝒰₀) {{_ : ISmallCategory S}} (X : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ⁺ ⊔ ⨆ 𝑗 ⁺) where
--   field {{CategoryInstance}} : ICategory X 𝑗
--         colim : (D : Diagram (category S) (category X ᵒᵖ)) -> Limit D
-- open ICategory⍮With_ShapedColimits {{...}} public

-- record ICategory⍮With_ShapedLimits (S : SmallCategory) (X : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ⁺ ⊔ ⨆ 𝑗 ⁺) where
--   field {{CategoryInstance}} : ICategory X 𝑗
--         lim : (D : Diagram S (category X)) -> Limit D
-- open ICategory⍮With_ShapedLimits {{...}} public

-- record ICategory⍮With_ShapedColimits (S : 𝒰₀) {{_ : ISmallCategory S}} (X : 𝒰 𝑖) 𝑗 : 𝒰 (𝑖 ⁺ ⊔ ⨆ 𝑗 ⁺) where
--   field {{CategoryInstance}} : ICategory X 𝑗
--         colim : (D : Diagram (category S) (category X ᵒᵖ)) -> Limit D
-- open ICategory⍮With_ShapedColimits {{...}} public





-- diagramPair : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} (a b : X) -> Diagram (smallCategory 𝟚) (category X)
-- diagramPair a b = diagram (λ {₀ -> a ; ₁ -> b})

-- limPair : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} (a b : X) -> Limit (diagramPair a b)
-- limPair a b = lim (diagramPair a b)

-- eval-Diagram : ∀{X : Category 𝑖} -> Functor (Category:Free (ForgetCategory X)) X
-- ⟨ eval-Diagram ⟩ a = a
-- IFunctor.map (of eval-Diagram) = map-eval
-- IFunctor.functoriality-id (of eval-Diagram) = refl
-- IFunctor.functoriality-◆ (of eval-Diagram) = {!!}

free-Diagram : ∀{X : Category 𝑖} {Q : Quiver (ℓ₀ , ℓ₀ , ℓ₀)} -> (f : QuiverHom Q (ForgetCategory X)) -> Diagram (Category:Free Q) X
free-Diagram {X = X} f =
  let f1 = Functor:comp-Cat (map-Category:Free f) (eval-Category:Free)
  in f1


data 𝟚 : 𝒰₀ where
  ₀ ₁ : 𝟚

instance
  ICategory:𝟚 = of Category:Discrete 𝟚


-- ⧼_,_⧽ : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} {a b c : X} -> (f : Hom a b) (g : Hom a c) -> Hom a (b × c)
-- ⧼_,_⧽ f g = {!!}


{-

--------------------------------------------------------------------
-- Instance
data 𝟚 : 𝒰₀ where
  ₀ : 𝟚
  ₁ : 𝟚

ISmallCategory:Discrete : ∀{X : 𝒰₀} -> ISmallCategory X
ICategory.Hom ISmallCategory:Discrete = {!!}
ICategory.id ISmallCategory:Discrete = {!!}
ICategory._◆_ ISmallCategory:Discrete = {!!}
ICategory.unit-l-◆ ISmallCategory:Discrete = {!!}
ICategory.unit-r-◆ ISmallCategory:Discrete = {!!}
ICategory.assoc-l-◆ ISmallCategory:Discrete = {!!}

-- ICategory.Hom ISmallCategory:Discrete (lift x) (lift y) = x ≡ y
-- ICategory.id ISmallCategory:Discrete = refl
-- ICategory._◆_ ISmallCategory:Discrete p q = p ∙ q

instance
  ISmallCategory:𝟚 : ISmallCategory 𝟚
  ISmallCategory:𝟚 = ISmallCategory:Discrete

instance
  IFunctor:FromDiscrete : ∀{X : 𝒰₀} -> {Y : Category 𝑖} -> {f : Lift X -> ⟨ Y ⟩} -> IFunctor (category (Lift X) {{ISmallCategory:Discrete}}) Y f
  IFunctor.map IFunctor:FromDiscrete = {!!}
  IFunctor.functoriality-id IFunctor:FromDiscrete = {!!}
  IFunctor.functoriality-◆ IFunctor:FromDiscrete = {!!}

Shape = SmallCategory
Shape:𝟚 : Shape
⟨ Shape:𝟚 ⟩ = 𝟚
of Shape:𝟚 = ISmallCategory:𝟚


_+_ : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedColimits X}} (a b : X) -> X
_+_ a b = ⟨ ⟨ colim (diagram (λ {₀ -> a ; ₁ -> b})) ⟩ ⟩

diagramPair : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} (a b : X) -> Diagram (smallCategory 𝟚) (category X)
diagramPair a b = diagram (λ {₀ -> a ; ₁ -> b})

limPair : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} (a b : X) -> Limit (diagramPair a b)
limPair a b = lim (diagramPair a b)

_×_ : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} (a b : X) -> X
_×_ a b = ⟨ ⟨ limPair a b ⟩ ⟩
-- _×_ a b = ⟨ ⟨ lim (diagram (λ {₀ -> a ; ₁ -> b})) ⟩ ⟩

-- TODO: Resolve: why do I need to do the following?
instance
  ICone:FromLimit : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} -> {d : Diagram Shape:𝟚 (category X)} -> ICone d (⟨ ⟨ lim d ⟩ ⟩)
  ICone:FromLimit {d = d} = ⟨ lim d ⟩ .Impl

π₀ : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} {a b : X} -> Hom (a × b) a
π₀ = ▲

π₁ : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} {a b : X} -> Hom (a × b) b
π₁ = ▲

⧼_,_⧽ : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} {a b c : X} -> (f : Hom a b) (g : Hom a c) -> Hom a (b × c)
⧼_,_⧽ f g = {!!}

instance
  IFunctor:× : {X : 𝒰 (𝑖 ⁺)} {{_ : ICategory⍮With(𝟚)ShapedLimits X}} {a : X} -> IFunctor (category X) (category X) (a ×_)
  IFunctor.map (IFunctor:× {a = a}) f = ⧼ π₀ , π₁ ◆ f ⧽
  IFunctor.functoriality-id IFunctor:× = {!!}
  IFunctor.functoriality-◆ IFunctor:× = {!!}


--------------------------------------------------------------------
-- Instances for categories


--------------------------------------------------------------------
-- Examples

record ParallelPair (X : Category 𝑖) : 𝒰 (𝑖 ⁺) where
  field source target : ⟨ X ⟩
        arr₀ arr₁ : Hom source target

open ParallelPair public

record Coequalizer-Cocone {X : Category 𝑖} (P : ParallelPair X) : 𝒰 (𝑖 ⁺) where
  field top : ⟨ X ⟩
        side : Hom (P .target) top
        coequalizes : (arr₀ P) ◆ side ≡ (arr₁ P) ◆ side

hasCoequalizer : (X : Category 𝑖) -> 𝒰 (𝑖 ⁺)
hasCoequalizer X = ∀ (P : ParallelPair X) -> Coequalizer-Cocone P

-- ParallelPair : Category 𝑖 -> 𝒰 (𝑖 ⁺)
-- ParallelPair X = ∑ λ (A : ⟨ X ⟩) -> ∑ λ B -> (Hom A B ×-𝒰 Hom A B)


-}
