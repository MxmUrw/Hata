
module Verification.Core.Algebra.Pointed.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Definition

record isPointed (X : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor isPointed:byDefinition
  field pt : X

open isPointed {{...}} public

module _ (𝑖 : 𝔏) where
  Pointed = 𝒰 𝑖 :& isPointed
  macro 𝐏𝐭𝐝 = #structureOn Pointed
macro 𝐏𝐭𝐝₀ = #structureOn (Pointed ℓ₀)

module _ (A : Pointed 𝑖) (B : Pointed 𝑗) where
  record isPointedHom (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    constructor isPointedHom:byDefinition
    field ptmap : f pt ≡ pt

  open isPointedHom {{...}} public

  PointedHom = _ :& isPointedHom

module _ {A : Pointed 𝑖} {B : Pointed 𝑗} where

  record _∼-PointedHom_ (f g : PointedHom A B) : 𝒰 (𝑖 ､ 𝑗) where
    field ⟨_⟩ : ⟨ f ⟩ ≡ ⟨ g ⟩

  instance
    isSetoid:PointedHom : isSetoid (PointedHom A B)
    isSetoid:PointedHom = setoid _∼-PointedHom_ {!!} {!!} {!!}

instance
  isPointed:Maybe : ∀{A : 𝒰 𝑖} -> isPointed (Maybe A)
  isPointed:Maybe = isPointed:byDefinition nothing

