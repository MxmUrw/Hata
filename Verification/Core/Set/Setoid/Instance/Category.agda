
module Verification.Core.Set.Setoid.Instance.Category where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition

module _ {A B : Setoid 𝑖} where
  -- instance
  --   isSetoid:SetoidHom-Base : isSetoid {𝑘} (Hom-Base SetoidHom A B)
  --   isSetoid:SetoidHom-Base = {!!} -- isSetoid:Hom-Base
  module _ (f g : SetoidHom A B) where
    record _∼-SetoidHom_ : 𝒰 𝑖 where
      constructor pointwise
      field ⟨_⟩ : ∀(a) -> ⟨ f ⟩ a ∼ ⟨ g ⟩ a

    open _∼-SetoidHom_ public

  instance
    isSetoid:SetoidHom : isSetoid (SetoidHom A B)
    isSetoid:SetoidHom = isSetoid:byDef _∼-SetoidHom_ (pointwise (λ a → refl)) {!!} {!!}

module _ {A : Setoid 𝑖} where


  instance
    isSetoidHom:id : isSetoidHom A A id-𝒰
    isSetoidHom:id = record { cong-∼ = λ p → p }
    -- isSetoidHom.preserves-∼ isSetoidHom:id p = p

  id-𝐒𝐭𝐝 : SetoidHom A A
  id-𝐒𝐭𝐝 = ′ id-𝒰 ′

module _ {A : Setoid 𝑖} {B : Setoid 𝑗} {C : Setoid 𝑘}  where
  -- instance
  isSetoidHom:◆ : {f : SetoidHom A B} {g : SetoidHom B C} -> isSetoidHom A C (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)
  isSetoidHom:◆ {f} {g} = record { cong-∼ = λ p → cong-∼ {{of g}} (cong-∼ {{of f}} p) }


  _◆-𝐒𝐭𝐝_ : (f : SetoidHom A B) (g : SetoidHom B C) -> SetoidHom A C
  _◆-𝐒𝐭𝐝_ f g = ′ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩ ′ {{isSetoidHom:◆ {f = f} {g = g}}}

instance
  isCategory:Setoid : ∀{𝑗 : 𝔏 ^ 2} -> isCategory (Setoid 𝑗)
  isCategory.Hom isCategory:Setoid = SetoidHom
  isCategory.isSetoid:Hom isCategory:Setoid = isSetoid:SetoidHom
  isCategory.id isCategory:Setoid = id-𝐒𝐭𝐝
  isCategory._◆_ isCategory:Setoid = _◆-𝐒𝐭𝐝_
  isCategory.unit-l-◆ isCategory:Setoid = {!!}
  isCategory.unit-r-◆ isCategory:Setoid = {!!}
  isCategory.unit-2-◆ isCategory:Setoid = {!!}
  isCategory.assoc-l-◆ isCategory:Setoid = {!!}
  isCategory.assoc-r-◆ isCategory:Setoid = {!!}
  isCategory._◈_ isCategory:Setoid = {!!}
  -- isCategory.Hom' isCategory:Setoid = SetoidHom
  -- isCategory.isSetoid:Hom isCategory:Setoid = it
  -- isCategory.id isCategory:Setoid = incl id-𝐒𝐭𝐝
  -- isCategory._◆_ isCategory:Setoid f g = incl (⟨ f ⟩ ◆-𝐒𝐭𝐝 ⟨ g ⟩)
  -- isCategory.unit-l-◆ isCategory:Setoid = {!!}
  -- isCategory.unit-r-◆ isCategory:Setoid = {!!}
  -- isCategory.unit-2-◆ isCategory:Setoid = {!!}
  -- isCategory.assoc-l-◆ isCategory:Setoid = {!!}
  -- isCategory.assoc-r-◆ isCategory:Setoid = {!!}
  -- isCategory._◈_ isCategory:Setoid = {!!}

module _ (𝑖 : 𝔏 ^ 2) where
  macro 𝐒𝐭𝐝 = #structureOn (Setoid 𝑖)

-- Std : ∀(𝑖) -> Category _
-- Std 𝑖 = ′ Setoid 𝑖 ′

  -- isCategory.Hom' (isCategory:Setoid {𝑗}) = SetoidHom
  -- isCategory.id (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory._◆_ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.unit-l-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.unit-r-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.unit-2-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.assoc-l-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.assoc-r-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory._◈_ (isCategory:Setoid {𝑗}) = {!!}



