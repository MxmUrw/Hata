
module Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Natural.Instance.Category

-- record hasGrothendieckSum (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
--   field ⨊ : A -> B

-- open hasGrothendieckSum {{...}} public

module _ {𝒞 : Category 𝑖} where


  record ⨊ᵘ (F : Functor 𝒞 (𝐂𝐚𝐭 𝑗)) : 𝒰 ((𝑖 ⌄ 0) ⊔ (𝑗 ⌄ 0)) where
    constructor _,_
    field bas : ⟨ 𝒞 ⟩
    field fib : ⟨ ⟨ F ⟩ bas ⟩

  open ⨊ᵘ public using (bas ; fib)
  -- open ⨊ {{...}} public using (fib)

  module _ (F : Functor 𝒞 (𝐂𝐚𝐭 𝑗)) where
    macro
      ⨊ = #structureOn (⨊ᵘ F)

  -- instance
  --   hasGrothendieckSum:𝐂𝐚𝐭 : hasGrothendieckSum (Functor 𝒞 (𝐂𝐚𝐭 𝑗)) _
  --   hasGrothendieckSum:𝐂𝐚𝐭 = record { ⨊ = ⨊ }


  module _ {F : Functor 𝒞 (𝐂𝐚𝐭 𝑗)} where
    private
      instance
        isCategory:F : ∀{b : ⟨ 𝒞 ⟩} -> isCategory (⟨ ⟨ F ⟩ b ⟩)
        isCategory:F {b} = of ⟨ F ⟩ b

      instance
        isSetoid:F : ∀{b : ⟨ 𝒞 ⟩} {x y : ⟨ ⟨ F ⟩ b ⟩} -> isSetoid (x ⟶ y)
        isSetoid:F {b} = isSetoid:Hom {{of ⟨ F ⟩ b}}

    record Hom-⨊ (a b : ⨊ F) : 𝒰 ((𝑖 ⌄ 1) ､ (𝑗 ⌄ 1)) where
      constructor _,_
      field bas : bas a ⟶ bas b
      field fib : Hom (⟨ map bas ⟩ (fib a)) (fib b)

    open Hom-⨊ public

    module _ {a b : ⨊ F} where
      record _∼-Hom-⨊_ (f g : Hom-⨊ a b) : 𝒰 (𝑖 ⌄ 2 ､ 𝑗 ⌄ 2) where
        constructor _,_
        field ∼-bas : bas f ∼ bas g
        field ∼-fib : fib f ∼ ⟨ ⟨ cong-∼ ∼-bas ⟩ ⟩ _ ◆ fib g

      instance
        isSetoid:Hom-⨊ : isSetoid (Hom-⨊ a b)
        isSetoid:Hom-⨊ = isSetoid:byDef _∼-Hom-⨊_ {!!} {!!} {!!}


    instance
      isCategory:⨊ : isCategory (⨊ F)
      isCategory.Hom isCategory:⨊          = Hom-⨊
      isCategory.isSetoid:Hom isCategory:⨊ = isSetoid:Hom-⨊
      isCategory.id isCategory:⨊           = {!!}
      isCategory._◆_ isCategory:⨊          = {!!}
      isCategory.unit-l-◆ isCategory:⨊     = {!!}
      isCategory.unit-r-◆ isCategory:⨊     = {!!}
      isCategory.unit-2-◆ isCategory:⨊     = {!!}
      isCategory.assoc-l-◆ isCategory:⨊    = {!!}
      isCategory.assoc-r-◆ isCategory:⨊    = {!!}
      isCategory._◈_ isCategory:⨊          = {!!}





