
module Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Category.Instance.ProductMonoid
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Iso
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Product

-- instance
--   isCategory:× : ∀{𝒞 𝒟 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{_ : isCategory {𝑗} 𝒟}} -> isCategory {𝑗} (𝒞 ×-𝒰 𝒟)
--   isCategory:× = {!!}


module _ (X : 𝒰 𝑖) {{_ : isSetoid {𝑗} X}} where
  Eq : X -> X -> 𝒰 _
  Eq a b = a ∼ b


private instance
  _ = isCategory:×

module MonoidalNotation (𝒞 : Category 𝑖) {{isMonoid:this : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)}}
                                         {{isFunctor:⋆ : isFunctor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞 ⋆⃨}} where

  infixl 70 _⊗_ _⇃⊗⇂_

  _⊗_ : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  _⊗_ = _⋆_

  αₘ = assoc-l-⋆ {{isMonoid:this}}
  λₘ = unit-l-⋆ {{isMonoid:this}}
  ρₘ = unit-r-⋆ {{isMonoid:this}}

  ⊗⃨ : Functor (𝒞 × 𝒞) 𝒞
  ⊗⃨ = ⋆⃨

  _⇃⊗⇂_ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) (g : c ⟶ d) -> (a ⋆ c ⟶ b ⋆ d)
  _⇃⊗⇂_ = λ₊ (map {{of ⊗⃨}})

  𝖨𝖽 = ◌

  𝖨𝖽⊗ : Functor 𝒞 𝒞
  𝖨𝖽⊗ = ⧼ Const 𝖨𝖽 , id ⧽ ◆ ⋆⃨

  ⊗𝖨𝖽 : Functor 𝒞 𝒞
  ⊗𝖨𝖽 = ⧼ id , Const 𝖨𝖽 ⧽ ◆ ⋆⃨

  [⊗]⊗ : Functor ((𝒞 ×-𝐂𝐚𝐭 𝒞) ×-𝐂𝐚𝐭 𝒞) 𝒞
  [⊗]⊗ = map-⊓ (⊗⃨ , id) ◆ ⊗⃨

  ⊗[⊗] : Functor (𝒞 ×-𝐂𝐚𝐭 (𝒞 ×-𝐂𝐚𝐭 𝒞)) 𝒞
  ⊗[⊗] = map-⊓ (id , ⊗⃨) ◆ ⊗⃨

  ⊗[⊗]' : Functor ((𝒞 ×-𝐂𝐚𝐭 𝒞) ×-𝐂𝐚𝐭 𝒞) 𝒞
  ⊗[⊗]' = ⟨ assoc-l-⋆ ⟩ ◆ ⊗[⊗]

  -- aaa = 𝖨𝖽
  -- bbb = 𝖨𝖽
  -- ccc = 𝖨𝖽


record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  constructor monoidal
  field {{isMonoid:this}} : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)

  field {{isFunctor:⋆}} : isFunctor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞 ⋆⃨

  field compat-Monoidal-⋆ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (p : a ≅ b) -> (q : c ≅ d)
                            -> ⟨ p ≀⋆≀ q ⟩ ∼ map (⟨ p ⟩ , ⟨ q ⟩)

  open MonoidalNotation 𝒞 {{isMonoid:this}} {{isFunctor:⋆}} public

  -- field {{isNaturalIso:unit-l-⋆}} : isNaturalIso 𝖨𝖽⊗ id (unit-l-⋆ {{isMonoid:this}})
  -- field {{isNaturalIso:unit-r-⋆}} : isNaturalIso ⊗𝖨𝖽 id (unit-r-⋆ {{isMonoid:this}})
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') (λ {((a , b) , c)} -> assoc-l-⋆ {{isMonoid:this}} {a = a} {b} {c})

  -- field triangle-Monoidal : ∀{a b : ⟨ 𝒞 ⟩} -> Eq ((a ⋆ 𝖨𝖽) ⋆ b ⟶ a ⋆ b)
  --                                             (⟨ ρₘ ⟩ ⇃⊗⇂ id)
  --                                             (⟨ αₘ ⟩ ◆ (id ⇃⊗⇂ ⟨ λₘ ⟩))

  -- field pentagon-Monoidal : ∀{a b c d : ⟨ 𝒞 ⟩} -> Eq (((a ⋆ b) ⋆ c) ⋆ d ⟶ a ⋆ (b ⋆ (c ⋆ d)))
  --                                            (⟨ αₘ ⟩ ◆ ⟨ αₘ ⟩)
  --                                            ((⟨ αₘ ⟩ ⇃⊗⇂ id) ◆ ⟨ αₘ ⟩ ◆ (id ⇃⊗⇂ ⟨ αₘ ⟩))

  -- field {{isNaturalIso:unit-l-⋆}} : isNaturalIso 𝖨𝖽⊗ id λₘ
  -- field {{isNaturalIso:unit-r-⋆}} : isNaturalIso ⊗𝖨𝖽 id ρₘ
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') assoc-l-⋆

  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso (𝖨𝖽⊗) (⊗𝖨𝖽) {!!}
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') {!!}
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') (λ {((a , b) , c)} -> {!!})
  -- assoc-l-⋆ {{isMonoid:this}} {a = a} {b} {c})





open isMonoidal {{...}} public

MonoidalCategory : ∀ 𝑖 -> 𝒰 _
MonoidalCategory 𝑖 = Category 𝑖 :& isMonoidal


module _ {𝒞 : 𝒰 _} {{_ : MonoidalCategory 𝑖 on 𝒞}} where

  ⨂-𝔽 : ∀{n} -> (𝔽ʳ n -> 𝒞) -> 𝒞
  ⨂-𝔽 = {!!}


module _ {𝑖} where
  instance
    isCategory:MonoidalCategory : isCategory {{!!}} (MonoidalCategory 𝑖)
    isCategory:MonoidalCategory = {!!}

macro
  𝐌𝐨𝐧𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
  𝐌𝐨𝐧𝐂𝐚𝐭 𝑖 = #structureOn (MonoidalCategory 𝑖)


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{MP : isMonoid (𝒞 since isSetoid:byCategory)}} where
  instance
    isMonoid:LiftCat : isMonoid (Lift-Cat {𝑘} 𝒞 since isSetoid:byCategory)
    isMonoid._⋆_ isMonoid:LiftCat =  λ a b -> lift (lower a ⋆ lower b)
    isMonoid.◌ isMonoid:LiftCat = lift ◌
    isMonoid.unit-l-⋆ isMonoid:LiftCat = incl ⟨ unit-l-⋆ ⟩ since record { inverse-◆ = incl (inverse-◆ (of (unit-l-⋆ {{MP}}))) ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }
    isMonoid.unit-r-⋆ isMonoid:LiftCat = incl ⟨ unit-r-⋆ ⟩ since record { inverse-◆ = incl (inverse-◆ (of (unit-r-⋆ {{MP}}))) ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }
    isMonoid.assoc-l-⋆ isMonoid:LiftCat = incl ⟨ assoc-l-⋆ ⟩ since record { inverse-◆ = incl (inverse-◆ (of (assoc-l-⋆ {{MP}}))) ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }
    isMonoid._`cong-⋆`_ isMonoid:LiftCat = {!!}

module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where
  instance
    isMonoidal:Lift : {{_ : isMonoidal ′ 𝒞 ′}} -> isMonoidal ′ Lift-Cat {𝑘} 𝒞 ′
    isMonoidal.isMonoid:this isMonoidal:Lift = isMonoid:LiftCat
    isFunctor.map (isMonoidal.isFunctor:⋆ isMonoidal:Lift) = λ (incl x , incl y) → incl (map (x , y))
    isFunctor.isSetoidHom:map (isMonoidal.isFunctor:⋆ isMonoidal:Lift) = {!!}
    isFunctor.functoriality-id (isMonoidal.isFunctor:⋆ isMonoidal:Lift) = {!!}
    isFunctor.functoriality-◆ (isMonoidal.isFunctor:⋆ isMonoidal:Lift) = {!!}
    isMonoidal.compat-Monoidal-⋆ isMonoidal:Lift = {!!}
    -- isMonoid._⋆_ (isMonoidal.isMonoid:this isMonoidal:Lift) = λ a b -> lift (lower a ⋆ lower b)
    -- isMonoid.◌ (isMonoidal.isMonoid:this isMonoidal:Lift) = lift ◌
    -- isMonoid.unit-l-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    -- isMonoid.unit-r-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    -- isMonoid.assoc-l-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    -- -- isMonoid.assoc-r-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    -- isMonoid._`cong-⋆`_ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    -- isMonoidal.compat-Monoidal-⋆ isMonoidal:Lift p q = {!!}
    -- isMonoidal.isFunctor:⋆ isMonoidal:Lift = {!!}
    -- isMonoidal.isNaturalIso:unit-l-⋆ isMonoidal:Lift = {!!}
    -- isMonoidal.isNaturalIso:unit-r-⋆ isMonoidal:Lift = {!!}
    -- isMonoidal.isNaturalIso:assoc-l-⋆ isMonoidal:Lift = {!!}
    -- isMonoidal.triangle-Monoidal isMonoidal:Lift = {!!}
    -- isMonoidal.pentagon-Monoidal isMonoidal:Lift = {!!}


































{-




module Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Fin.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Category.Instance.ProductMonoid
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Iso
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Experimental.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Product

-- instance
--   isCategory:× : ∀{𝒞 𝒟 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} {{_ : isCategory {𝑗} 𝒟}} -> isCategory {𝑗} (𝒞 ×-𝒰 𝒟)
--   isCategory:× = {!!}


module _ (X : 𝒰 𝑖) {{_ : isSetoid {𝑗} X}} where
  Eq : X -> X -> 𝒰 _
  Eq a b = a ∼ b


private instance
  _ = isCategory:×


record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  constructor monoidal
  field {{isMonoid:this}} : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)

  private instance
    _ : isSetoid ⟨ 𝒞 ⟩
    _ = isSetoid:byCategory

  αₘ = assoc-l-⋆ {{isMonoid:this}}
  λₘ = unit-l-⋆ {{isMonoid:this}}
  ρₘ = unit-r-⋆ {{isMonoid:this}}

  field {{isFunctor:⋆}} : isFunctor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞 ⋆⃨

  ⊗⃨ : Functor (𝒞 × 𝒞) 𝒞
  ⊗⃨ = ⋆⃨

  _⇃⊗⇂_ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) (g : c ⟶ d) -> (a ⋆ c ⟶ b ⋆ d)
  _⇃⊗⇂_ = λ₊ (map {{of ⊗⃨}})

  𝖨𝖽 = ◌

  𝖨𝖽⊗ : Functor 𝒞 𝒞
  𝖨𝖽⊗ = ⧼ Const 𝖨𝖽 , id ⧽ ◆ ⋆⃨

  ⊗𝖨𝖽 : Functor 𝒞 𝒞
  ⊗𝖨𝖽 = ⧼ id , Const 𝖨𝖽 ⧽ ◆ ⋆⃨

  field {{isNaturalIso:unit-l-⋆}} : isNaturalIso 𝖨𝖽⊗ id λₘ
  field {{isNaturalIso:unit-r-⋆}} : isNaturalIso ⊗𝖨𝖽 id ρₘ


  field compat-Monoidal-⋆ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (p : a ≅ b) -> (q : c ≅ d)
                            -> ⟨ p ≀⋆≀ q ⟩ ∼ map (⟨ p ⟩ , ⟨ q ⟩)

  [⊗]⊗ : Functor ((𝒞 ×-𝐂𝐚𝐭 𝒞) ×-𝐂𝐚𝐭 𝒞) 𝒞
  [⊗]⊗ = map-⊓ (⊗⃨ , id) ◆ ⊗⃨

  ⊗[⊗] : Functor (𝒞 ×-𝐂𝐚𝐭 (𝒞 ×-𝐂𝐚𝐭 𝒞)) 𝒞
  ⊗[⊗] = map-⊓ (id , ⊗⃨) ◆ ⊗⃨

  ⊗[⊗]' : Functor ((𝒞 ×-𝐂𝐚𝐭 𝒞) ×-𝐂𝐚𝐭 𝒞) 𝒞
  ⊗[⊗]' = ⟨ assoc-l-⋆ ⟩ ◆ ⊗[⊗]

  field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') αₘ

  -- field triangle-Monoidal : ∀{a b : ⟨ 𝒞 ⟩} -> Eq ((a ⋆ 𝖨𝖽) ⋆ b ≅ a ⋆ b)
  --                                             (ρₘ ≀⋆≀ refl)
  --                                             (αₘ ∙ (refl ≀⋆≀ λₘ))

  -- field pentagon-Monoidal : ∀{a b c d : ⟨ 𝒞 ⟩} -> Eq (((a ⋆ b) ⋆ c) ⋆ d ≅ a ⋆ (b ⋆ (c ⋆ d)))
  --                                            (αₘ ∙ αₘ)
  --                                            ((αₘ ≀⋆≀ refl) ∙ αₘ ∙ (refl ≀⋆≀ αₘ))

  field triangle-Monoidal : ∀{a b : ⟨ 𝒞 ⟩} -> Eq ((a ⋆ 𝖨𝖽) ⋆ b ⟶ a ⋆ b)
                                              (⟨ ρₘ ⟩ ⇃⊗⇂ id)
                                              (⟨ αₘ ⟩ ◆ (id ⇃⊗⇂ ⟨ λₘ ⟩))

  field pentagon-Monoidal : ∀{a b c d : ⟨ 𝒞 ⟩} -> Eq (((a ⋆ b) ⋆ c) ⋆ d ⟶ a ⋆ (b ⋆ (c ⋆ d)))
                                             (⟨ αₘ ⟩ ◆ ⟨ αₘ ⟩)
                                             ((⟨ αₘ ⟩ ⇃⊗⇂ id) ◆ ⟨ αₘ ⟩ ◆ (id ⇃⊗⇂ ⟨ αₘ ⟩))




open isMonoidal {{...}} public

MonoidalCategory : ∀ 𝑖 -> 𝒰 _
MonoidalCategory 𝑖 = Category 𝑖 :& isMonoidal


module _ {𝒞 : 𝒰 _} {{_ : MonoidalCategory 𝑖 on 𝒞}} where

  infixl 70 _⊗_

  _⊗_ : 𝒞 -> 𝒞 -> 𝒞
  _⊗_ = _⋆_

  assoc-l-⊗ : ∀{a b c : 𝒞} -> ((a ⊗ b) ⊗ c) ⟶ (a ⊗ (b ⊗ c))
  assoc-l-⊗ = {!!}

  unit-r-⊗ : ∀{a : 𝒞} -> (a ⊗ ◌) ⟶ a
  unit-r-⊗ = {!!}


  ⨂-𝔽 : ∀{n} -> (𝔽ʳ n -> 𝒞) -> 𝒞
  ⨂-𝔽 = {!!}


module _ {𝑖} where
  instance
    isCategory:MonoidalCategory : isCategory {{!!}} (MonoidalCategory 𝑖)
    isCategory:MonoidalCategory = {!!}

macro
  𝐌𝐨𝐧𝐂𝐚𝐭 : ∀ 𝑖 -> SomeStructure
  𝐌𝐨𝐧𝐂𝐚𝐭 𝑖 = #structureOn (MonoidalCategory 𝑖)


module _ {𝒞 : 𝒰 𝑖} {{𝒞p : isCategory {𝑗} 𝒞}} where
  instance
    isMonoidal:Lift : {{_ : isMonoidal ′ 𝒞 ′}} -> isMonoidal ′ Lift-Cat {𝑘} 𝒞 ′
    isMonoid._⋆_ (isMonoidal.isMonoid:this isMonoidal:Lift) = λ a b -> lift (lower a ⋆ lower b)
    isMonoid.◌ (isMonoidal.isMonoid:this isMonoidal:Lift) = lift ◌
    isMonoid.unit-l-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid.unit-r-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid.assoc-l-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    -- isMonoid.assoc-r-⋆ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoid._`cong-⋆`_ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoidal.compat-Monoidal-⋆ isMonoidal:Lift p q = {!!}
    isMonoidal.isFunctor:⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:unit-l-⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:unit-r-⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:assoc-l-⋆ isMonoidal:Lift = {!!}
    isMonoidal.triangle-Monoidal isMonoidal:Lift = {!!}
    isMonoidal.pentagon-Monoidal isMonoidal:Lift = {!!}
    -- isMonoidal.map-⊗ isMonoidal:Lift f g = {!!}

-}
