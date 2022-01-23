
module Verification.Core.Category.Std.Functor.Representable2 where

--
-- NOTE:
--   This is a rewriting of Verification.Core.Category.Std.Functor.Representable,
--   to be merged when more complete.
--

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid


instance
  hasU:∏' : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> hasU (∀(a) -> B a) _ _
  getU (hasU:∏' {A = A} {B}) = ∀(a) -> B a
  getP (hasU:∏' {𝑖} {𝑗} {A = A} {B}) u = isAnything {A = ∀(a) -> B a} u (ℓ₀)
  reconstruct (hasU:∏' {A = A} {B}) (x , _) = x
  destructEl (hasU:∏' {A = A} {B}) f = f
  destructP (hasU:∏' {A = A} {B}) _ = record {}


-- We need isomorphisms across universe levels of presheaves
record isIso-𝐒𝐭𝐝 {a : Setoid 𝑖} {b : Setoid 𝑗} (f : SetoidHom a b) : 𝒰 (𝑖 ､ 𝑗) where
  field inverse-𝐒𝐭𝐝 : SetoidHom b a
        inv-r-◆-𝐒𝐭𝐝 : (f ◆-𝐒𝐭𝐝 inverse-𝐒𝐭𝐝) ∼ id-𝐒𝐭𝐝
        inv-l-◆-𝐒𝐭𝐝 : (inverse-𝐒𝐭𝐝 ◆-𝐒𝐭𝐝 f) ∼ id-𝐒𝐭𝐝
open isIso-𝐒𝐭𝐝 {{...}} public

_≅-𝐒𝐭𝐝_ : (A : Setoid 𝑖) (B : Setoid 𝑗) -> 𝒰 (𝑖 ､ 𝑗)
A ≅-𝐒𝐭𝐝 B = (SetoidHom A B) :& isIso-𝐒𝐭𝐝


Co𝐏𝐒𝐡 : (𝒞 : Category 𝑖) -> ∀ 𝑗 -> 𝒰 _
Co𝐏𝐒𝐡 𝒞 𝑗 = 𝐅𝐮𝐧𝐜 𝒞 (𝐒𝐭𝐝 𝑗)

module _ {𝒞 : Category 𝑖} where
  module _ (A : Co𝐏𝐒𝐡 𝒞 𝑗) (B : Co𝐏𝐒𝐡 𝒞 𝑘) where
    record isPresheafMap (f : ∀(c : ⟨ 𝒞 ⟩) -> SetoidHom (⟨ A ⟩ c) (⟨ B ⟩ c)) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
      -- field naturality : ∀{c d : ⟨ 𝒞 ⟩} -> 

    PresheafMap = _ :& isPresheafMap

  record isIso-Co𝐏𝐒𝐡 {A : Co𝐏𝐒𝐡 𝒞 𝑗} {B : Co𝐏𝐒𝐡 𝒞 𝑘} (f : PresheafMap A B) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field inverse-◆-Co𝐏𝐒𝐡 : PresheafMap B A

  open isIso-Co𝐏𝐒𝐡 public

  _≅-Co𝐏𝐒𝐡_ : (A : Co𝐏𝐒𝐡 𝒞 𝑗) (B : Co𝐏𝐒𝐡 𝒞 𝑘) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘)
  _≅-Co𝐏𝐒𝐡_ A B = PresheafMap A B :& isIso-Co𝐏𝐒𝐡


--
-- the hom functors
--
module _ {C : 𝒰 𝑖} {{_ : isCategory {𝑖₁} C}} where
  private
    𝒞 : Category _
    𝒞 = ′ C ′

  --
  -- first the contravariant hom
  --

  module _ (b : C) where
    ℎ𝑜𝑚ᵘ : C -> 𝐒𝐭𝐝 _
    ℎ𝑜𝑚ᵘ a = a ⟶ b

    -- macro ℎ𝑜𝑚 = #structureOn ℎ𝑜𝑚ᵘ


  module _ {a : C} where
    instance
      isFunctor:ℎ𝑜𝑚 : isFunctor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _) (ℎ𝑜𝑚ᵘ a)
      isFunctor.map isFunctor:ℎ𝑜𝑚 = {!!}
      isFunctor.isSetoidHom:map isFunctor:ℎ𝑜𝑚 = {!!}
      isFunctor.functoriality-id isFunctor:ℎ𝑜𝑚 = {!!}
      isFunctor.functoriality-◆ isFunctor:ℎ𝑜𝑚 = {!!}

  module _ (a : C) where
    --
    -- It seems that resolution cannot distinguish
    -- between ℎ𝑜𝑚 and ℎ𝑜𝑚ᵒᵖ functor instances,
    -- so we cannot use this as macro, but need
    -- to specialize to Functor.
    --
    -- macro ℎ𝑜𝑚ᵒᵖ = #structureOn ℎ𝑜𝑚ᵒᵖᵘ
    --

    ℎ𝑜𝑚 : Functor (𝒞 ᵒᵖ) (𝐒𝐭𝐝 _)
    ℎ𝑜𝑚 = ′ ℎ𝑜𝑚ᵘ a ′

  --
  -- now the covariant hom
  --
  module _ (a : C) where
    ℎ𝑜𝑚ᵒᵖᵘ : C -> 𝐒𝐭𝐝 _
    ℎ𝑜𝑚ᵒᵖᵘ b = a ⟶ b


  module _ {a : C} where

    map-ℎ𝑜𝑚ᵒᵖ : ∀{x y : C} -> x ⟶ y -> ℎ𝑜𝑚ᵒᵖᵘ a x ⟶ ℎ𝑜𝑚ᵒᵖᵘ a y
    map-ℎ𝑜𝑚ᵒᵖ f = (λ g -> g ◆ f) since record { cong-∼ = λ p → p ◈ refl }

    instance
      isFunctor:ℎ𝑜𝑚ᵒᵖ : isFunctor 𝒞 (𝐒𝐭𝐝 _) (ℎ𝑜𝑚ᵒᵖᵘ a)
      isFunctor.map isFunctor:ℎ𝑜𝑚ᵒᵖ = map-ℎ𝑜𝑚ᵒᵖ
      isFunctor.isSetoidHom:map isFunctor:ℎ𝑜𝑚ᵒᵖ = {!!}
      isFunctor.functoriality-id isFunctor:ℎ𝑜𝑚ᵒᵖ = {!!}
      isFunctor.functoriality-◆ isFunctor:ℎ𝑜𝑚ᵒᵖ = {!!}


  module _ (a : C) where
    --
    -- It seems that resolution cannot distinguish
    -- between ℎ𝑜𝑚 and ℎ𝑜𝑚ᵒᵖ functor instances,
    -- so we cannot use this as macro, but need
    -- to specialize to Functor.
    --
    -- macro ℎ𝑜𝑚ᵒᵖ = #structureOn ℎ𝑜𝑚ᵒᵖᵘ
    --

    ℎ𝑜𝑚ᵒᵖ : Functor 𝒞 (𝐒𝐭𝐝 _)
    ℎ𝑜𝑚ᵒᵖ = ′ ℎ𝑜𝑚ᵒᵖᵘ a ′


module _ {𝒞 : Category 𝑖} where
  record isCorepresented (F : Co𝐏𝐒𝐡 𝒞 𝑗) (x : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field corep : F ≅-Co𝐏𝐒𝐡 ℎ𝑜𝑚ᵒᵖ x

  open isCorepresented public

  record isRepresented (F : Co𝐏𝐒𝐡 (𝒞 ᵒᵖ) 𝑗) (x : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field rep : F ≅-Co𝐏𝐒𝐡 ℎ𝑜𝑚 x

  open isRepresented public
  -- Corep : (Functor 𝒞 (𝐒𝐭𝐝 _)) -> 𝒰 _
  -- Corep F = Structure (isCorep F)
