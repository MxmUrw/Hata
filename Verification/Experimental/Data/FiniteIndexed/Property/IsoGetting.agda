
module Verification.Experimental.Data.FiniteIndexed.Property.IsoGetting where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Contradiction
-- open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Experimental.Data.List.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.SeparatingFamily

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Instance.SeparatingFamily

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting


module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where
  instance
    hasIsoGetting:𝐅𝐢𝐧𝐈𝐱 : hasIsoGetting (𝐅𝐢𝐧𝐈𝐱 A)
    hasIsoGetting:𝐅𝐢𝐧𝐈𝐱 = record { getIso = lem-1 }
      where
        lem-1 : (a b : FiniteIndexed A) → Maybe (a ≅ b)
        lem-1 a b with ♮ ⟨ a ⟩ ≟-Str ♮ ⟨ b ⟩
        ... | yes p = let q : ⟨ a ⟩ ∼ ⟨ b ⟩
                          q = injective-♮-Free-𝐌𝐨𝐧 {a = ⟨ a ⟩} {b = ⟨ b ⟩} (≡-Str→≡ p)
                          r : 𝑒𝑙 ⟨ a ⟩ ≅ 𝑒𝑙 ⟨ b ⟩
                          r = cong-∼ q
                      in right (incl ⟨ r ⟩ since record { inverse-◆ = incl (inverse-◆ (of r)) ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} })
        ... | no ¬p = nothing




