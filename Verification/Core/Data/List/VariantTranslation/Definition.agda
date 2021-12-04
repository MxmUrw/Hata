
module Verification.Core.Data.List.VariantTranslation.Definition where

open import Verification.Core.Conventions

open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Base.Definition
open import Verification.Core.Data.List.Variant.Base.Instance.Monoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Definition
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Setoid
open import Verification.Core.Data.List.Variant.FreeMonoid.Instance.Monoid


module _ {A : 𝒰 𝑖} where
  -- the inclusion from lists
  ι-⋆List : List A -> ⋆List A
  ι-⋆List ⦋⦌ = ◌
  ι-⋆List (a ∷ as) = incl a ⋆ ι-⋆List as

  instance
    hasInclusion:List,⋆List : hasInclusion (List A) (⋆List A)
    hasInclusion:List,⋆List = inclusion ι-⋆List

  pres-⋆-ι-⋆List : ∀{as bs : List A} -> ι (as ⋆ bs) ∼ ι as ⋆ ι bs
  pres-⋆-ι-⋆List {⦋⦌} {bs} = unit-l-⋆ ⁻¹
  pres-⋆-ι-⋆List {x ∷ as} {bs} = refl ≀⋆≀ pres-⋆-ι-⋆List ∙ assoc-r-⋆

  -- the normalization into lists
  ♮-⋆List : ⋆List A -> List A
  ♮-⋆List (incl x) = x ∷ []
  ♮-⋆List (a ⋆-⧜ b) = ♮-⋆List a ⋆ ♮-⋆List b
  ♮-⋆List ◌-⧜ = ⦋⦌

  instance
    hasNormalization:⋆List,List : hasNormalization (⋆List A) (List A)
    hasNormalization:⋆List,List = normalization ♮-⋆List

  surj-♮-⋆List : ∀{a : ⋆List A} -> ι (♮ a) ∼ a
  surj-♮-⋆List {incl x} = unit-r-⋆
  surj-♮-⋆List {a ⋆-⧜ a₁} = pres-⋆-ι-⋆List ∙ surj-♮-⋆List ≀⋆≀ surj-♮-⋆List
  surj-♮-⋆List {◌-⧜} = refl

  injective-♮-⋆List : ∀{a b : ⋆List A} -> ♮ a ≡ ♮ b -> a ∼ b
  injective-♮-⋆List p = surj-♮-⋆List ⁻¹ ∙ ≡→∼ (cong ι p) ∙ surj-♮-⋆List





