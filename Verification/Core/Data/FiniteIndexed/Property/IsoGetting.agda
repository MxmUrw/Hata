
module Verification.Core.Data.FiniteIndexed.Property.IsoGetting where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Contradiction
-- open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.SeparatingFamily

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Indexed.Instance.SeparatingFamily

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting


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




