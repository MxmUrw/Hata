
module Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category
-- open import Verification.Core.Data.Indexed.Duplicate
-- open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.Indexed.Instance.Monoid
-- open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Data.List.Variant.Binary.Natural


-------------------------
-- Finite coproducts via category of functors

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid

module _ {𝒞 : Category 𝑖} {{_ : hasFiniteCoproducts 𝒞}} where

  ⨆ᶠᵘ : ∀{n : 人ℕ} -> 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞 -> ⟨ 𝒞 ⟩
  ⨆ᶠᵘ {incl x}   d = ⟨ d ⟩ (member incl)
  ⨆ᶠᵘ {a ⋆-⧜ b}  d = ⨆ᶠᵘ (leftᶠ ◆-𝐂𝐚𝐭 d) ⊔ ⨆ᶠᵘ (rightᶠ ◆-𝐂𝐚𝐭 d)
  ⨆ᶠᵘ {◌-⧜}      d = ⊥

  -----------------------------------------
  -- Properties of ⨆ᶠ
  module _ {n : 人ℕ} where
    macro ⨆ᶠ = #structureOn (⨆ᶠᵘ {n})

  ∼-⨆ᶠ:byPointwise : ∀{n : 人ℕ} -> {F G : 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞} -> (∀(i : [ n ]ᶠ) -> ⟨ F ⟩ i ≅ ⟨ G ⟩ i) -> ⨆ᶠ F ≅ ⨆ᶠ G
  ∼-⨆ᶠ:byPointwise = {!!}

  ⨆ᶠ≀ : {n : 人ℕ} {F G : 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞} -> (F ∼ G) -> ⨆ᶠ F ≅ ⨆ᶠ G
  ⨆ᶠ≀ {incl x} {F} {G} p = ⟨ ⟨ p ⟩ ⟩ _ since record
                         { inverse-◆ = ⟨ ⟨ p ⟩⁻¹ ⟩ _
                         ; inv-r-◆ = ⟨ inv-r-◆ (of p) ⟩ _
                         ; inv-l-◆ = ⟨ inv-l-◆ (of p) ⟩ _
                         }
  ⨆ᶠ≀ {m ⋆-⧜ n} {F} {G} p = ⨆ᶠ≀ (refl ≀◆≀-𝐂𝐚𝐭 p) ≀⊔≀ ⨆ᶠ≀ (refl ≀◆≀-𝐂𝐚𝐭 p)
  ⨆ᶠ≀ {◌-⧜} {F} {G} p = refl-≅



  --------------------------------------------------------------------------------
  -- [Lemma]
  -- | If a functor |F : 𝒞 → 𝒟| preserves coproducts, then it also
  --   preserves |⨆ᶠ|.
  -- //
  -- [Proof]
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗}
         {{_ : hasFiniteCoproducts 𝒞}} {{_ : hasFiniteCoproducts 𝒟}}
         (F : Functor 𝒞 𝒟) {{_ : isFiniteCoproductPreserving F}}
         where
  preserves-⨆ᶠ : ∀{n} -> ∀{x : 𝐅𝐮𝐧𝐜 [ n ]ᶠ 𝒞} -> ⟨ F ⟩ (⨆ᶠ x) ≅ ⨆ᶠ (x ◆-𝐂𝐚𝐭 F)
  preserves-⨆ᶠ {incl x₁} {x} = refl-≅
  preserves-⨆ᶠ {n ⋆-⧜ n₁} {x} =
    ⟨ F ⟩ (⨆ᶠ (leftᶠ ◆-𝐂𝐚𝐭 x) ⊔ ⨆ᶠ (rightᶠ ◆-𝐂𝐚𝐭 x))

    ⟨ preserves-⊔ ⟩-≅

    (⟨ F ⟩ (⨆ᶠ (leftᶠ ◆-𝐂𝐚𝐭 x)) ⊔ (⟨ F ⟩ (⨆ᶠ (rightᶠ ◆-𝐂𝐚𝐭 x))))

    ⟨ preserves-⨆ᶠ ≀⊔≀ preserves-⨆ᶠ ⟩-≅

    ((⨆ᶠ (leftᶠ ◆-𝐂𝐚𝐭 x ◆-𝐂𝐚𝐭 F)) ⊔ (⨆ᶠ (rightᶠ ◆-𝐂𝐚𝐭 x ◆-𝐂𝐚𝐭 F)))

    ⟨ ⨆ᶠ≀ assoc-l-◆-𝐂𝐚𝐭 ≀⊔≀ ⨆ᶠ≀ assoc-l-◆-𝐂𝐚𝐭 ⟩-≅

    ⨆ᶠ (x ◆-𝐂𝐚𝐭 F)

    ∎-≅

  -- preserves-⊔ ∙-≅ ({!!} ≀⊔≀ {!!})
  preserves-⨆ᶠ {◌-⧜} {x} = preserves-⊥

  -- //






module _ (𝑗 : 𝔏) (𝒞 : Category 𝑖) {{_ : hasFiniteCoproducts 𝒞}} where
  record isFiniteCoproductGenerated : 𝒰 (𝑖 ､ 𝑗 ⁺) where
    -- constructor isFiniteCoproductGenerated:byDefinition
    field fcgProp : ⟨ 𝒞 ⟩ -> 𝒰 𝑗
    field fcgPropIsoStable : ∀{a b : ⟨ 𝒞 ⟩} -> a ≅ b -> fcgProp a -> fcgProp b
    field fcgSize : ⟨ 𝒞 ⟩ -> 人ℕ
    field fcg : (a : ⟨ 𝒞 ⟩) -> 𝐅𝐮𝐧𝐜 [ fcgSize a ]ᶠ 𝒞
    field fcgHasProp : ∀{a : ⟨ 𝒞 ⟩} -> ∀(i : [ fcgSize a ]ᶠ)-> fcgProp (⟨ fcg a ⟩ i)
    field fcgIso : ∀ (a : ⟨ 𝒞 ⟩) -> a ≅ ⨆ᶠ (fcg a)

  open isFiniteCoproductGenerated {{...}} public



--------------------------------------------------------------
-- Properties of FCG

-- [Lemma]
-- | If there is a coproduct preserving, eso functor |𝒞 → 𝒟|,
--   and |𝒞| is FCG, then so is |𝒟|.
--
-- //
-- [Proof]
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒞}} {{_ : hasFiniteCoproducts 𝒟}} (F : Functor 𝒞 𝒟) where
  module _ {{_ : isFiniteCoproductPreserving F}} {{_ : isEssentiallySurjective F}} where
    module _ {{_ : isFiniteCoproductGenerated 𝑘 𝒞}} where
      private
        fcg'Size : ⟨ 𝒟 ⟩ -> 人ℕ
        fcg'Size a = fcgSize (eso a)

        fcg'Prop : ⟨ 𝒟 ⟩ -> 𝒰 𝑘
        fcg'Prop a = fcgProp (eso a)

        fcg' : (a : ⟨ 𝒟 ⟩) → Functor [ fcg'Size a ]ᶠ 𝒟
        fcg' a = fcg (eso a) ◆-𝐂𝐚𝐭 F

        fcg'Iso : (a : ⟨ 𝒟 ⟩) → a ≅ ⨆ᶠ (fcg' a)
        fcg'Iso a = a

                    ⟨ sym-≅ inv-eso ⟩-≅

                    ⟨ F ⟩ (eso a)

                    ⟨ cong-≅ (fcgIso (eso a)) ⟩-≅

                    ⟨ F ⟩ (⨆ᶠ (fcg (eso a)))

                    ⟨ preserves-⨆ᶠ F ⟩-≅

                    ⨆ᶠ (fcg' a)

                    ∎-≅

      fcg'HasProp : {a : ⟨ 𝒟 ⟩} (i : [ fcg'Size a ]ᶠᵘ) → fcg'Prop (⟨ fcg' a ⟩ i)
      fcg'HasProp {a} i =
        let P = fcgHasProp {a = eso a} i
        in {!!}

      isFiniteCoproductGenerated:byIsFiniteCoproductPreserving : isFiniteCoproductGenerated 𝑘 𝒟
      isFiniteCoproductGenerated:byIsFiniteCoproductPreserving = record
        { fcgSize = fcg'Size
        ; fcgProp = fcg'Prop
        ; fcg = fcg'
        ; fcgIso = fcg'Iso
        ; fcgHasProp = {!!}
        ; fcgPropIsoStable = {!!}
        }



-- //



open import Verification.Core.Category.Std.Functor.Equivalence
-- [Corollary]
-- | If there is an equivalence of categories |F : 𝒞 ≅ 𝒟|, and |𝒞| is cfg, then so is |𝒟|.
-- //

-- [Proof]
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {{_ : hasFiniteCoproducts 𝒞}} {{_ : hasFiniteCoproducts 𝒟}} (Fp : 𝒞 ≅-𝐂𝐚𝐭 𝒟) where
  module _ {{_ : isFiniteCoproductGenerated 𝑘 𝒞}} where
    private
      F : Functor 𝒞 𝒟
      F = ′ ⟨ Fp ⟩ ′

    isFiniteCoproductGenerated:by≅-𝐂𝐚𝐭 : isFiniteCoproductGenerated 𝑘 𝒟
    isFiniteCoproductGenerated:by≅-𝐂𝐚𝐭 = isFiniteCoproductGenerated:byIsFiniteCoproductPreserving F
      where
        instance
          P-0 : isFiniteCoproductPreserving F
          P-0 = {!!}

        instance
          P-1 : isEssentiallySurjective F
          P-1 = isEssentiallySurjective:byIsIso-𝐂𝐚𝐭

-- //
