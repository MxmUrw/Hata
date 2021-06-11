
module Verification.Experimental.Category.Std.Fibration.Specific.Fam.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything

private variable
  𝒞 : Category 𝑖

record isFamily (𝒞 : Category 𝑖) (A : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor family
  field _■ : A -> ⟨ 𝒞 ⟩
  infix 100 _■

open isFamily {{...}} public

Family : ∀ (𝒞 : Category 𝑖) -> (𝑗 : 𝔏) -> 𝒰 _
Family 𝒞 𝑗 = 𝒰 (𝑗) :& isFamily 𝒞

macro
  𝐅𝐚𝐦 : ∀(𝒞 : Category 𝑖) -> ∀ 𝑗 -> SomeStructure
  𝐅𝐚𝐦 𝒞 𝑗 = #structureOn (Family 𝒞 𝑗)

module _ {𝒞 : Category 𝑖} (X : Family 𝒞 𝑗) (Y : Family 𝒞 𝑘) where
  record isFamilyHom (f : ⟨ X ⟩ -> ⟨ Y ⟩) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    field map-■ : ∀{a : ⟨ X ⟩} -> a ■ ⟶ f a ■

  FamilyHom = _ :& isFamilyHom


instance
  isCategory:Family : ∀{𝒞 : Category 𝑖} -> isCategory (_ , ⨆ 𝑖 ⊔ 𝑗) (Family 𝒞 𝑗)
  isCategory.Hom' isCategory:Family = FamilyHom
  isCategory.isSetoid:Hom isCategory:Family = {!!}
  isCategory.id isCategory:Family = {!!}
  isCategory._◆_ isCategory:Family = {!!}
  isCategory.unit-l-◆ isCategory:Family = {!!}
  isCategory.unit-r-◆ isCategory:Family = {!!}
  isCategory.unit-2-◆ isCategory:Family = {!!}
  isCategory.assoc-l-◆ isCategory:Family = {!!}
  isCategory.assoc-r-◆ isCategory:Family = {!!}
  isCategory._◈_ isCategory:Family = {!!}

-- private
--   _* : 𝐓𝐲𝐩𝐞 𝑖 -> 𝐂𝐚𝐭
--   _* A = {!!} since {!!}

module _ {𝒞 : Category 𝑗} {𝑖} where
  private
    Forget : 𝐅𝐚𝐦 𝒞 𝑖 -> 𝐓𝐲𝐩𝐞 _
    Forget 𝔔 = ⟨ 𝔔 ⟩

  instance
    Register:ForgetFam = register[ "" ] Forget

  instance
    isFunctor:ForgetFam : isFunctor (𝐅𝐚𝐦 𝒞 𝑖) (𝐓𝐲𝐩𝐞 _) Forget
    isFunctor.map isFunctor:ForgetFam = λ f -> incl ⟨ ⟨ f ⟩ ⟩
    isFunctor.isSetoidHom:map isFunctor:ForgetFam = {!!}
    isFunctor.functoriality-id isFunctor:ForgetFam = {!!}
    isFunctor.functoriality-◆ isFunctor:ForgetFam = {!!}


