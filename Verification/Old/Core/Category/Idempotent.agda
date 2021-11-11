
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Idempotent where


open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Functor
-- open import Verification.Old.Core.Category.Instance.Cat
-- open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Limit.Kan.Definition
open import Verification.Old.Core.Category.Limit.Kan.Equalizer
open import Verification.Old.Core.Category.Limit.Kan.Terminal
open import Verification.Old.Core.Category.Instance.SmallCategories

module _ {X : 𝒰 𝑖} {{_ : ICategory X 𝑗}} where
  record IIdempotent {a : X} (f : a ⟶ a) : 𝒰 (𝑖 ､ 𝑗) where
    field idempotent : f ◆ f ≣ f
open IIdempotent {{...}} public
unquoteDecl Idempotent mkIdempotent = #struct "Idpt" (quote IIdempotent) "f" Idempotent mkIdempotent

module _ {𝒞 : Category 𝑖} {{_ : hasEqualizers 𝒞}} where
  -- instance _ = of 𝒞

  Normal : {x : ⟨ 𝒞 ⟩} -> (I : Idempotent x) -> ⟨ 𝒞 ⟩
  Normal I = Eq ⟨ I ⟩ id

  module _ {x : ⟨ 𝒞 ⟩} {I : x ⟶ x} {{_ : IIdempotent I}} where
    private
      D : Functor 𝔼 𝒞
      D = Diagram-𝔼 I id

      xcone : Cone D x
      xcone = Cone-𝔼 I (idempotent ∙ unit-r-◆ ⁻¹)

      normalize-impl : Diagram-𝟙 x ⟶ _
      normalize-impl = free⁻¹ xcone

    normalize : x ⟶ lim D
    normalize = ⟨ normalize-impl ⟩ {↥ tt}


