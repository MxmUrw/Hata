
module Verification.Experimental.Set.Setoid.Instance.Category where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Category.Std.Category.Definition

module _ {A B : Setoid 𝑖} where
  instance
    isSetoid:SetoidHom-Base : isSetoid _ (Hom-Base SetoidHom A B)
    isSetoid:SetoidHom-Base = isSetoid:Hom-Base

module _ {A : Setoid 𝑖} where

  instance
    isSetoidHom:id : isSetoidHom A A id-𝒰
    isSetoidHom.preserves-∼ isSetoidHom:id p = p

  id-Std : SetoidHom A A
  id-Std = ′ id-𝒰 ′

module _ {A : Setoid 𝑖} {B : Setoid 𝑗} {C : Setoid 𝑘}  where
  -- instance
  isSetoidHom:◆ : {f : SetoidHom A B} {g : SetoidHom B C} -> isSetoidHom A C (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)
  isSetoidHom.preserves-∼ (isSetoidHom:◆ {f} {g}) p = preserves-∼ (preserves-∼ {{of f}} p)

  _◆-Std_ : (f : SetoidHom A B) (g : SetoidHom B C) -> SetoidHom A C
  _◆-Std_ f g = ′ ⟨ f ⟩ ◆-𝒰 ⟨ g ⟩ ′ {{isSetoidHom:◆ {f = f} {g = g}}}

instance
  isCategory:Setoid : ∀{𝑗 : 𝔏 ^ 2} -> isCategory _ (Setoid 𝑗)
  isCategory.Hom' isCategory:Setoid = SetoidHom
  isCategory.isSetoid:Hom isCategory:Setoid = it
  isCategory.id isCategory:Setoid = incl id-Std
  isCategory._◆_ isCategory:Setoid f g = incl (⟨ f ⟩ ◆-Std ⟨ g ⟩)
  isCategory.unit-l-◆ isCategory:Setoid = {!!}
  isCategory.unit-r-◆ isCategory:Setoid = {!!}
  isCategory.unit-2-◆ isCategory:Setoid = {!!}
  isCategory.assoc-l-◆ isCategory:Setoid = {!!}
  isCategory.assoc-r-◆ isCategory:Setoid = {!!}
  isCategory._◈_ isCategory:Setoid = {!!}

Std : ∀(𝑖) -> Category _
Std 𝑖 = ′ Setoid 𝑖 ′

  -- isCategory.Hom' (isCategory:Setoid {𝑗}) = SetoidHom
  -- isCategory.id (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory._◆_ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.unit-l-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.unit-r-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.unit-2-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.assoc-l-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory.assoc-r-◆ (isCategory:Setoid {𝑗}) = {!!}
  -- isCategory._◈_ (isCategory:Setoid {𝑗}) = {!!}



