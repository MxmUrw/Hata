
module Verification.Core.Category.Std.Limit.Cone.Colimit.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2


module _ {𝒥 : Category 𝑖} {𝒞 : Category 𝑗} where
  record Cocone (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    constructor cocone
    field pt : ⟨ 𝒞 ⟩
    field ◺ : F ⟶ Const pt

  open Cocone public

  module _ (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) where
    macro 𝐂𝐨𝐜𝐨𝐧𝐞 = #structureOn (Cocone F)


  module _ {F : 𝐅𝐮𝐧𝐜 𝒥 𝒞} where
    record Hom-Cocone (c d : Cocone F) : 𝒰 (𝑖 ､ 𝑗) where
      field pt : pt c ⟶ pt d
      field ◺ : ◺ c ◆ map-Const pt ∼ ◺ d

    open Hom-Cocone public

    module _ {c d : Cocone F} where
      record _∼-Hom-Cocone_ (f g : Hom-Cocone c d) : 𝒰 (𝑖 ､ 𝑗) where
        constructor incl
        field ⟨_⟩ : pt f ∼ pt g

      open _∼-Hom-Cocone_ public

      refl-∼-Hom-Cocone : ∀{f : Hom-Cocone c d} -> f ∼-Hom-Cocone f
      refl-∼-Hom-Cocone = incl refl

      sym-∼-Hom-Cocone : ∀{f g : Hom-Cocone c d} -> f ∼-Hom-Cocone g -> g ∼-Hom-Cocone f
      sym-∼-Hom-Cocone (incl p) = incl (p ⁻¹)

      trans-∼-Hom-Cocone : ∀{f g h : Hom-Cocone c d} -> f ∼-Hom-Cocone g -> g ∼-Hom-Cocone h -> f ∼-Hom-Cocone h
      trans-∼-Hom-Cocone (incl p) (incl q) = incl (p ∙ q)

      instance
        isSetoid:Hom-Cocone : isSetoid (Hom-Cocone c d)
        isSetoid:Hom-Cocone = isSetoid:byDef _∼-Hom-Cocone_ refl-∼-Hom-Cocone sym-∼-Hom-Cocone trans-∼-Hom-Cocone

    id-𝐂𝐨𝐜𝐨𝐧𝐞 : ∀{c : Cocone F} -> Hom-Cocone c c
    id-𝐂𝐨𝐜𝐨𝐧𝐞 = record
      { pt = id
      ; ◺ = (refl ◈ functoriality-id) ∙ unit-r-◆
      }

    _◆-𝐂𝐨𝐜𝐨𝐧𝐞_ : ∀{c d e : Cocone F} -> Hom-Cocone c d -> Hom-Cocone d e -> Hom-Cocone c e
    _◆-𝐂𝐨𝐜𝐨𝐧𝐞_ f g = record
      { pt = pt f ◆ pt g
      ; ◺ = (refl ◈ functoriality-◆) ∙ assoc-r-◆ ∙ (◺ f ◈ refl) ∙ ◺ g
      }

    instance
      isCategory:Cocone : isCategory (Cocone F)
      isCategory.Hom isCategory:Cocone = Hom-Cocone
      isCategory.isSetoid:Hom isCategory:Cocone = isSetoid:Hom-Cocone
      isCategory.id isCategory:Cocone = id-𝐂𝐨𝐜𝐨𝐧𝐞
      isCategory._◆_ isCategory:Cocone = _◆-𝐂𝐨𝐜𝐨𝐧𝐞_
      isCategory.unit-l-◆ isCategory:Cocone = incl unit-l-◆
      isCategory.unit-r-◆ isCategory:Cocone = incl unit-r-◆
      isCategory.unit-2-◆ isCategory:Cocone = incl unit-2-◆
      isCategory.assoc-l-◆ isCategory:Cocone = incl assoc-l-◆
      isCategory.assoc-r-◆ isCategory:Cocone = incl assoc-r-◆
      isCategory._◈_ isCategory:Cocone = λ p q -> incl (⟨ p ⟩ ◈ ⟨ q ⟩)

  record isColimit (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) (rep : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field colimitCocone : F ⟶ Const rep
    field colimitUniversal : isInitial (cocone rep colimitCocone)

  open isColimit public

  -- record hasColimit (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
  --   field rep : 𝐂𝐨𝐜𝐨𝐧𝐞 F
  --   field {{isTerminal:rep}} : isInitial rep




