
module Verification.Core.Category.Std.Category.Structured.SeparatingFamily where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition


module _ (𝒞 : Category 𝑖) where

  record isSeparatingFamily {𝑗 : 𝔏} {I : 𝒰 𝑗} (F : I -> ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field separate : ∀{a b : ⟨ 𝒞 ⟩} -> (ϕ ψ : a ⟶ b) -> (∀ {i : I} -> ∀ (ξ : F i ⟶ a) -> ξ ◆ ϕ ∼ ξ ◆ ψ) -> ϕ ∼ ψ

  open isSeparatingFamily {{...}} public

record hasSeparatingFamily (𝑗 : 𝔏) (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field {Separator} : 𝒰 𝑗
  field separator : Separator -> ⟨ 𝒞 ⟩
  field {{isSeparatingFamily:seperators}} : isSeparatingFamily 𝒞 separator

open hasSeparatingFamily {{...}} public





