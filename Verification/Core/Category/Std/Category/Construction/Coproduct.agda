
module Verification.Core.Category.Std.Category.Construction.Coproduct where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.CategoryLike
open import Verification.Core.Category.Std.Category.Construction.Id
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso


--------------------------------------------------------------
-- Showing that _+_ on universes lifts to categories

module _ {𝒞 : 𝒰 𝑖} {𝒟 : 𝒰 𝑗} {{_ : isCategory {𝑖₁} 𝒞}} {{_ : isCategory {𝑗₁} 𝒟}} where

  --
  -- Implementation note:
  -- We cannot use data types for the definition of +-Hom,
  -- since then they would also contain the objects of
  -- 𝒞 or 𝒟, and then the universe level of (𝒞 + 𝒟),
  -- would not match that of 𝒞 or 𝒟, even if `level 𝒞 ≡ level 𝒟`
  --

  +-Hom : (a b : (𝒞 + 𝒟)) -> 𝒰 (fst 𝑖₁ ､ fst 𝑗₁)
  +-Hom (left a) (left b) = Lift {fst 𝑖₁ ､ fst 𝑗₁} {fst 𝑖₁} (a ⟶ b)
  +-Hom (left a) (just b) = ⊥-𝒰
  +-Hom (just a) (left b) = ⊥-𝒰
  +-Hom (just a) (just b) = Lift {fst 𝑖₁ ､ fst 𝑗₁} {fst 𝑗₁} (a ⟶ b)

  id-+ : ∀{a : 𝒞 + 𝒟} -> +-Hom a a
  id-+ {left x} = ↥ id
  id-+ {just x} = ↥ id

  _◆-+_ : ∀{a b c : 𝒞 + 𝒟} -> +-Hom a b -> +-Hom b c -> +-Hom a c
  _◆-+_ {a = left a}  {b = left b}  {c = left c}  f g = lift (lower f ◆ lower g)
  _◆-+_ {a = right a} {b = right b} {c = right c} f g = lift (lower f ◆ lower g)

  _∼-+-Hom_ : {a b : 𝒞 + 𝒟} (f g : +-Hom a b) -> 𝒰 (snd 𝑖₁ ､ snd 𝑗₁)
  _∼-+-Hom_ {a = left a}  {b = left b}  (lift f) (lift g) = Lift {snd 𝑖₁ ､ snd 𝑗₁} (f ∼ g)
  _∼-+-Hom_ {a = right a} {b = right b} (lift f) (lift g) = Lift {snd 𝑖₁ ､ snd 𝑗₁} (f ∼ g)

  refl-∼-+-Hom : ∀{a b : 𝒞 + 𝒟} {f : +-Hom a b} -> f ∼-+-Hom f
  refl-∼-+-Hom {a = left a}  {b = left b}  = ↥ refl
  refl-∼-+-Hom {a = right a} {b = right b} = ↥ refl

  sym-∼-+-Hom : ∀{a b : 𝒞 + 𝒟} {f g : +-Hom a b} -> f ∼-+-Hom g -> g ∼-+-Hom f
  sym-∼-+-Hom {a = left a}  {b = left b}  (↥ p) = ↥ (sym p)
  sym-∼-+-Hom {a = right a} {b = right b} (↥ p) = ↥ (sym p)

  trans-∼-+-Hom : ∀{a b : 𝒞 + 𝒟} {f g h : +-Hom a b} -> f ∼-+-Hom g -> g ∼-+-Hom h -> f ∼-+-Hom h
  trans-∼-+-Hom {a = left a}  {b = left b}  (↥ p) (↥ q) = ↥ (p ∙ q)
  trans-∼-+-Hom {a = right a} {b = right b} (↥ p) (↥ q) = ↥ (p ∙ q)

  module _ {a b : 𝒞 + 𝒟} where
    instance
      isSetoid:+-Hom : isSetoid (+-Hom a b)
      isSetoid:+-Hom = isSetoid:byDef _∼-+-Hom_ refl-∼-+-Hom sym-∼-+-Hom trans-∼-+-Hom

  instance
    isCategory:+ : isCategory (𝒞 + 𝒟)
    isCategory.Hom isCategory:+ = +-Hom
    isCategory.isSetoid:Hom isCategory:+ = isSetoid:+-Hom
    isCategory.id isCategory:+         = id-+
    isCategory._◆_ isCategory:+        = _◆-+_ -- λ (f₀ , g₀) (f₁ , g₁) -> (f₀ ◆ f₁ , g₀ ◆ g₁)
    isCategory.unit-l-◆ isCategory:+   = {!!} -- unit-l-◆ , unit-l-◆
    isCategory.unit-r-◆ isCategory:+   = {!!} -- unit-r-◆ , unit-r-◆
    isCategory.unit-2-◆ isCategory:+   = {!!} -- unit-2-◆ , unit-2-◆
    isCategory.assoc-l-◆ isCategory:+  = {!!} -- assoc-l-◆ , assoc-l-◆
    isCategory.assoc-r-◆ isCategory:+  = {!!} -- assoc-r-◆ , assoc-r-◆
    isCategory._◈_ isCategory:+        = {!!} -- λ (p₀ , q₀) (p₁ , q₁) -> (p₀ ◈ p₁ , q₀ ◈ q₁)

_+-𝐂𝐚𝐭_ : 𝐂𝐚𝐭 𝑖 -> 𝐂𝐚𝐭 𝑗 -> 𝐂𝐚𝐭 _
_+-𝐂𝐚𝐭_ 𝒞 𝒟 = 𝒞 + 𝒟

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{_ : isCategory {𝑖₁} A}} {{_ : isCategory {𝑗₁} B}} where
  private
    𝒜 : Category _
    𝒜 = ′ A ′

    ℬ : Category _
    ℬ = ′ B ′

  ι₀ᵘ-𝐂𝐚𝐭 : A -> A + B
  ι₀ᵘ-𝐂𝐚𝐭 = left

  ι₁ᵘ-𝐂𝐚𝐭 : B -> A + B
  ι₁ᵘ-𝐂𝐚𝐭 = right

  macro ι₀-𝐂𝐚𝐭 = #structureOn ι₀ᵘ-𝐂𝐚𝐭
  macro ι₁-𝐂𝐚𝐭 = #structureOn ι₁ᵘ-𝐂𝐚𝐭

  map-ι₀-𝐂𝐚𝐭 : ∀{a b : A} -> a ⟶ b -> Hom {{of 𝒜 +-𝐂𝐚𝐭 ℬ}} (left a) (left b)
  map-ι₀-𝐂𝐚𝐭 f = ↥ f

  map-ι₁-𝐂𝐚𝐭 : ∀{a b : B} -> a ⟶ b -> Hom {{of 𝒜 +-𝐂𝐚𝐭 ℬ}} (right a) (right b)
  map-ι₁-𝐂𝐚𝐭 f = ↥ f

  instance
    isFunctor:ι₀-𝐂𝐚𝐭 : isFunctor 𝒜 (𝒜 +-𝐂𝐚𝐭 ℬ) ι₀-𝐂𝐚𝐭
    isFunctor.map isFunctor:ι₀-𝐂𝐚𝐭 = map-ι₀-𝐂𝐚𝐭
    isFunctor.isSetoidHom:map isFunctor:ι₀-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-id isFunctor:ι₀-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-◆ isFunctor:ι₀-𝐂𝐚𝐭 = {!!}

  instance
    isFunctor:ι₁-𝐂𝐚𝐭 : isFunctor ℬ (𝒜 +-𝐂𝐚𝐭 ℬ) ι₁-𝐂𝐚𝐭
    isFunctor.map isFunctor:ι₁-𝐂𝐚𝐭 = map-ι₁-𝐂𝐚𝐭
    isFunctor.isSetoidHom:map isFunctor:ι₁-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-id isFunctor:ι₁-𝐂𝐚𝐭 = {!!}
    isFunctor.functoriality-◆ isFunctor:ι₁-𝐂𝐚𝐭 = {!!}

  module _ {𝒞 : Category 𝑘} (F : Functor 𝒜 𝒞 ×-𝒰 Functor ℬ 𝒞) where
    ⦗_⦘ᵘ-𝐂𝐚𝐭 : 𝒜 + ℬ -> ⟨ 𝒞 ⟩
    ⦗_⦘ᵘ-𝐂𝐚𝐭 = either (⟨ fst F ⟩) (⟨ snd F ⟩)
    -- macro ⦗_⦘-𝐂𝐚𝐭 = #structureOn ⦗_⦘ᵘ-𝐂𝐚𝐭

    map-⦗⦘-𝐂𝐚𝐭 : ∀{a b : 𝒜 + ℬ} -> (f : a ⟶ b) -> ⦗_⦘ᵘ-𝐂𝐚𝐭 a ⟶ ⦗_⦘ᵘ-𝐂𝐚𝐭 b
    map-⦗⦘-𝐂𝐚𝐭 {a = left a}  {b = left b}  (↥ f) = map f
    map-⦗⦘-𝐂𝐚𝐭 {a = right a} {b = right b} (↥ f) = map f

    instance
      isFunctor:⦗⦘-𝐂𝐚𝐭 : isFunctor (𝒜 +-𝐂𝐚𝐭 ℬ) 𝒞 ⦗_⦘ᵘ-𝐂𝐚𝐭
      isFunctor.map isFunctor:⦗⦘-𝐂𝐚𝐭 = map-⦗⦘-𝐂𝐚𝐭
      isFunctor.isSetoidHom:map isFunctor:⦗⦘-𝐂𝐚𝐭 = {!!}
      isFunctor.functoriality-id isFunctor:⦗⦘-𝐂𝐚𝐭 = {!!}
      isFunctor.functoriality-◆ isFunctor:⦗⦘-𝐂𝐚𝐭 = {!!}

    ⦗_⦘-𝐂𝐚𝐭 : Functor (𝒜 + ℬ) 𝒞
    ⦗_⦘-𝐂𝐚𝐭 = ′ ⦗_⦘ᵘ-𝐂𝐚𝐭 ′

--
-- Old implementation here:
--

{-
  data +-Hom : (a b : (𝒞 + 𝒟)) -> 𝒰 (𝑖 ､ (fst 𝑖₁) ､ 𝑗 ､ (fst 𝑗₁)) where
    left  : ∀{a b : 𝒞} -> a ⟶ b -> +-Hom (left a) (left b)
    right : ∀{a b : 𝒟} -> a ⟶ b -> +-Hom (right a) (right b)

  id-+ : ∀{a : 𝒞 + 𝒟} -> +-Hom a a
  id-+ {left x} = left id
  id-+ {just x} = right id

  _◆-+_ : ∀{a b c : 𝒞 + 𝒟} -> +-Hom a b -> +-Hom b c -> +-Hom a c
  left  f ◆-+ left  g = left (f ◆ g)
  right f ◆-+ right g = right (f ◆ g)

  data _∼-+-Hom_ : {a b : 𝒞 + 𝒟} (f g : +-Hom a b) -> 𝒰 (𝑖 ､ 𝑖₁ ､ 𝑗 ､ 𝑗₁) where
    left   : ∀{a b : 𝒞} -> {f g : a ⟶ b} -> f ∼ g -> left f ∼-+-Hom left g
    right  : ∀{a b : 𝒟} -> {f g : a ⟶ b} -> f ∼ g -> right f ∼-+-Hom right g

  refl-∼-+-Hom : ∀{a b : 𝒞 + 𝒟} {f : +-Hom a b} -> f ∼-+-Hom f
  refl-∼-+-Hom {f = left x} = left refl
  refl-∼-+-Hom {f = right x} = right refl

  sym-∼-+-Hom : ∀{a b : 𝒞 + 𝒟} {f g : +-Hom a b} -> f ∼-+-Hom g -> g ∼-+-Hom f
  sym-∼-+-Hom (left x) = left (sym x)
  sym-∼-+-Hom (right x) = right (sym x)

  trans-∼-+-Hom : ∀{a b : 𝒞 + 𝒟} {f g h : +-Hom a b} -> f ∼-+-Hom g -> g ∼-+-Hom h -> f ∼-+-Hom h
  trans-∼-+-Hom (left p) (left q) = left (p ∙ q)
  trans-∼-+-Hom (right p) (right q) = right (p ∙ q)


  module _ {a b : 𝒞 + 𝒟} where
    instance
      isSetoid:+-Hom : isSetoid (+-Hom a b)
      isSetoid:+-Hom = isSetoid:byDef _∼-+-Hom_ refl-∼-+-Hom sym-∼-+-Hom trans-∼-+-Hom


  instance
    isCategory:+ : isCategory (𝒞 + 𝒟)
    isCategory.Hom isCategory:+ = +-Hom
    isCategory.isSetoid:Hom isCategory:+ = isSetoid:+-Hom
    isCategory.id isCategory:+         = id-+
    isCategory._◆_ isCategory:+        = _◆-+_ -- λ (f₀ , g₀) (f₁ , g₁) -> (f₀ ◆ f₁ , g₀ ◆ g₁)
    isCategory.unit-l-◆ isCategory:+   = {!!} -- unit-l-◆ , unit-l-◆
    isCategory.unit-r-◆ isCategory:+   = {!!} -- unit-r-◆ , unit-r-◆
    isCategory.unit-2-◆ isCategory:+   = {!!} -- unit-2-◆ , unit-2-◆
    isCategory.assoc-l-◆ isCategory:+  = {!!} -- assoc-l-◆ , assoc-l-◆
    isCategory.assoc-r-◆ isCategory:+  = {!!} -- assoc-r-◆ , assoc-r-◆
    isCategory._◈_ isCategory:+        = {!!} -- λ (p₀ , q₀) (p₁ , q₁) -> (p₀ ◈ p₁ , q₀ ◈ q₁)
-}



