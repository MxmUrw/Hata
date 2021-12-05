
module Verification.Core.Data.FiniteIndexed.Property.IsoGetting where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition

open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.Universe.Instance.Category

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed
open import Verification.Core.Data.List.VariantTranslation.Definition



module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where
  instance
    hasIsoGetting:𝐅𝐢𝐧𝐈𝐱 : hasIsoGetting (𝐅𝐢𝐧𝐈𝐱 A)
    hasIsoGetting:𝐅𝐢𝐧𝐈𝐱 = record { getIso = lem-1 }
      where
        lem-1 : (a b : FiniteIndexed A) → Maybe (a ≅ b)
        lem-1 a b with ♮ ⟨ a ⟩ ≟-Str ♮ ⟨ b ⟩
        ... | yes p = let q : ⟨ a ⟩ ∼ ⟨ b ⟩
                          q = injective-♮-⋆List {a = ⟨ a ⟩} {b = ⟨ b ⟩} (≡-Str→≡ p)
                          r : 𝑒𝑙 ⟨ a ⟩ ≅ 𝑒𝑙 ⟨ b ⟩
                          r = cong-∼ q
                      in right (incl ⟨ r ⟩ since record { inverse-◆ = incl (inverse-◆ (of r)) ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} })
        ... | no ¬p = nothing




