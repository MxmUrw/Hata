
module Verification.Core.Category.Std.Category.Structured.Monoidal.DefinitionOptimized where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Product

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

  infixl 70 _⊗_

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


record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  constructor monoidal
  field {{isMonoid:this}} : isMonoid (⟨ 𝒞 ⟩ since isSetoid:byCategory)

  field {{isFunctor:⋆}} : isFunctor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞 ⋆⃨

  field compat-Monoidal-⋆ : ∀{a b c d : ⟨ 𝒞 ⟩} -> (p : a ≅ b) -> (q : c ≅ d)
                            -> ⟨ p ≀⋆≀ q ⟩ ∼ map (⟨ p ⟩ , ⟨ q ⟩)

  open MonoidalNotation 𝒞 {{isMonoid:this}} {{isFunctor:⋆}} public

  -- field {{isNaturalIso:unit-l-⋆}} : isNaturalIso 𝖨𝖽⊗ id λₘ
  -- field {{isNaturalIso:unit-r-⋆}} : isNaturalIso ⊗𝖨𝖽 id ρₘ
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') assoc-l-⋆

  field {{isNaturalIso:unit-l-⋆}} : isNaturalIso 𝖨𝖽⊗ id (unit-l-⋆ {{isMonoid:this}})
  field {{isNaturalIso:unit-r-⋆}} : isNaturalIso ⊗𝖨𝖽 id (unit-r-⋆ {{isMonoid:this}})
  field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') (λ {((a , b) , c)} -> assoc-l-⋆ {{isMonoid:this}} {a = a} {b} {c})
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso (𝖨𝖽⊗) (⊗𝖨𝖽) {!!}
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') {!!}
  -- field {{isNaturalIso:assoc-l-⋆}} : isNaturalIso ([⊗]⊗) (⊗[⊗]') (λ {((a , b) , c)} -> {!!})
  -- assoc-l-⋆ {{isMonoid:this}} {a = a} {b} {c})

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
    isMonoid._≀⋆≀_ (isMonoidal.isMonoid:this isMonoidal:Lift) = {!!}
    isMonoidal.compat-Monoidal-⋆ isMonoidal:Lift p q = {!!}
    isMonoidal.isFunctor:⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:unit-l-⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:unit-r-⋆ isMonoidal:Lift = {!!}
    isMonoidal.isNaturalIso:assoc-l-⋆ isMonoidal:Lift = {!!}
    isMonoidal.triangle-Monoidal isMonoidal:Lift = {!!}
    isMonoidal.pentagon-Monoidal isMonoidal:Lift = {!!}

