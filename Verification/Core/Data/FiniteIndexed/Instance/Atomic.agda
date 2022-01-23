

module Verification.Core.Data.FiniteIndexed.Instance.Atomic where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Discrete
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
-- open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Category.Construction.Coproduct
open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Functor.Representable2
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed

-- open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated
open import Verification.Core.Category.Std.Category.Structured.Atomic.Definition
open import Verification.Core.Category.Std.Limit.Representation.Colimit.Definition


module _ {I : 𝒰 𝑖} where
  𝑠𝑖𝑛𝑔𝑙 : I -> 𝐅𝐢𝐧𝐈𝐱 I
  𝑠𝑖𝑛𝑔𝑙 i = incl (incl i)

  module _ {𝑗 : 𝔏 ^ 3} {a : I} where
    isAtom:𝑠𝑖𝑛𝑔𝑙 : isAtom 𝑗 (𝑠𝑖𝑛𝑔𝑙 a)
    isAtom:𝑠𝑖𝑛𝑔𝑙 {𝒥} D {x} xP = record { corep = {!? since ?!} }
      where
        ϕ : (Const'' ′ ⟨ 𝒥 ⟩ ′ ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a))) ≅-Co𝐏𝐒𝐡 ℎ𝑜𝑚ᵒᵖ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)
        ϕ = ?
        -- ϕ : (Const'' ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a))) ≅-Co𝐏𝐒𝐡 ℎ𝑜𝑚ᵒᵖ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)
        -- ϕ = ?
        -- f : PresheafMap (Const'' ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a))) (ℎ𝑜𝑚ᵒᵖ (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x))
        -- f = ?

      -- let α = colimitCocone xP
      --     βᵘ : ∀(j : ⟨ 𝒥 ⟩) -> (𝑠𝑖𝑛𝑔𝑙 a ⟶ ⟨ D ⟩ j) -> 𝑠𝑖𝑛𝑔𝑙 a ⟶ x
      --     βᵘ j f = f ◆ ⟨ α ⟩ j
      --     instance
      --       isSetoidHom:β : ∀{j} -> isSetoidHom (𝑠𝑖𝑛𝑔𝑙 a ⟶ ⟨ D ⟩ j) (𝑠𝑖𝑛𝑔𝑙 a ⟶ x) (βᵘ j)
      --       isSetoidHom:β = record { cong-∼ = λ p → p ◈ refl }

      --     isNatural:β : isNatural (D ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a)) (Const (⟨ ℎ𝑜𝑚ᵒᵖ (𝑠𝑖𝑛𝑔𝑙 a) ⟩ x)) (λ j -> ′ βᵘ j ′)
      --     isNatural:β = natural {!!}
      -- in record
      --   { colimitCocone = (λ j -> ′ βᵘ j ′) since {!!}
      --   ; colimitUniversal = {!!}
      --   }

    -- isColimit.colimitCocone (isAtom:𝑠𝑖𝑛𝑔𝑙 D {x} xp) = {!!}
    -- isColimit.isTerminal:rep (isAtom:𝑠𝑖𝑛𝑔𝑙 D {x} xp) = {!!}





