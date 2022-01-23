
module Verification.Core.Category.Std.Limit.Cone.Limit.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2



module _ {𝒥 : Category 𝑖} {𝒞 : Category 𝑗} where
  record Cone (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
    constructor cone
    field pt : ⟨ 𝒞 ⟩
    field ◺ : Const pt ⟶ F

  open Cone public

  module _ (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) where
    macro 𝐂𝐨𝐧𝐞 = #structureOn (Cone F)


  module _ {F : 𝐅𝐮𝐧𝐜 𝒥 𝒞} where
    record Hom-Cone (c d : Cone F) : 𝒰 (𝑖 ､ 𝑗) where
      field pt : pt c ⟶ pt d
      field ◺ : map-Const pt ◆ ◺ d ∼ ◺ c

    open Hom-Cone public

    module _ {c d : Cone F} where
      record _∼-Hom-Cone_ (f g : Hom-Cone c d) : 𝒰 (𝑖 ､ 𝑗) where
        constructor incl
        field ⟨_⟩ : pt f ∼ pt g

      open _∼-Hom-Cone_ public

      refl-∼-Hom-Cone : ∀{f : Hom-Cone c d} -> f ∼-Hom-Cone f
      refl-∼-Hom-Cone = incl refl

      sym-∼-Hom-Cone : ∀{f g : Hom-Cone c d} -> f ∼-Hom-Cone g -> g ∼-Hom-Cone f
      sym-∼-Hom-Cone (incl p) = incl (p ⁻¹)

      trans-∼-Hom-Cone : ∀{f g h : Hom-Cone c d} -> f ∼-Hom-Cone g -> g ∼-Hom-Cone h -> f ∼-Hom-Cone h
      trans-∼-Hom-Cone (incl p) (incl q) = incl (p ∙ q)

      instance
        isSetoid:Hom-Cone : isSetoid (Hom-Cone c d)
        isSetoid:Hom-Cone = isSetoid:byDef _∼-Hom-Cone_ refl-∼-Hom-Cone sym-∼-Hom-Cone trans-∼-Hom-Cone

    id-𝐂𝐨𝐧𝐞 : ∀{c : Cone F} -> Hom-Cone c c
    id-𝐂𝐨𝐧𝐞 = record
      { pt = id
      ; ◺ = (functoriality-id ◈ refl) ∙ unit-l-◆
      }

    _◆-𝐂𝐨𝐧𝐞_ : ∀{c d e : Cone F} -> Hom-Cone c d -> Hom-Cone d e -> Hom-Cone c e
    _◆-𝐂𝐨𝐧𝐞_ f g = record
      { pt = pt f ◆ pt g
      ; ◺ = (functoriality-◆ ◈ refl) ∙ assoc-l-◆ ∙ (refl ◈ ◺ g) ∙ ◺ f
      }

    instance
      isCategory:Cone : isCategory (Cone F)
      isCategory.Hom isCategory:Cone = Hom-Cone
      isCategory.isSetoid:Hom isCategory:Cone = isSetoid:Hom-Cone
      isCategory.id isCategory:Cone = id-𝐂𝐨𝐧𝐞
      isCategory._◆_ isCategory:Cone = _◆-𝐂𝐨𝐧𝐞_
      isCategory.unit-l-◆ isCategory:Cone = incl unit-l-◆
      isCategory.unit-r-◆ isCategory:Cone = incl unit-r-◆
      isCategory.unit-2-◆ isCategory:Cone = incl unit-2-◆
      isCategory.assoc-l-◆ isCategory:Cone = incl assoc-l-◆
      isCategory.assoc-r-◆ isCategory:Cone = incl assoc-r-◆
      isCategory._◈_ isCategory:Cone = λ p q -> incl (⟨ p ⟩ ◈ ⟨ q ⟩)

  record isLimit (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) (rep : ⟨ 𝒞 ⟩) : 𝒰 (𝑖 ､ 𝑗) where
    field limitCocone : Const rep ⟶ F
    field limitUniversal : isTerminal (cone rep limitCocone)

  open isLimit public

  -- record hasLimit (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
  --   field rep : 𝐂𝐨𝐧𝐞 F
  --   field {{isTerminal:rep}} : isTerminal rep




