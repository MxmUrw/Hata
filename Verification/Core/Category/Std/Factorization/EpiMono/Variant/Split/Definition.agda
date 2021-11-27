
module Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.Morphism.Epi.Definition


module _ {𝒞' : Category 𝑖} {{_ : hasCoproducts 𝒞'}} where
  private macro 𝒞 = #structureOn ⟨ 𝒞' ⟩

  record isSplitEpiMonoFactorizable {a b : 𝒞} (f : a ⟶ b) : 𝒰 𝑖 where
    field image : 𝒞
    field rest : 𝒞
    field splitting : image ⊔ rest ≅ b
    field epiHom : a ⟶ image
    field {{isEpi:epiHom}} : isEpi epiHom
    field factors : f ◆ ⟨ splitting ⟩⁻¹ ∼ epiHom ◆ ι₀

  open isSplitEpiMonoFactorizable public

module _ (𝒞' : Category 𝑖) {{_ : hasCoproducts 𝒞'}} where

  private macro 𝒞 = #structureOn ⟨ 𝒞' ⟩

  record hasSplitEpiMonoFactorization : 𝒰 𝑖 where
    field factorize : ∀{a b : 𝒞} -> (f : a ⟶ b) -> isSplitEpiMonoFactorizable f

  open hasSplitEpiMonoFactorization {{...}} public








