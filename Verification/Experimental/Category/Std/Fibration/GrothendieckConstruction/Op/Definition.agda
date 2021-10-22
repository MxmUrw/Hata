
module Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Natural.Instance.Category

-- record hasGrothendieckSumOp (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
--   field ⨊ᵒᵖ : A -> B

-- open hasGrothendieckSumOp {{...}} public

module _ {𝒞 : Category 𝑖} where


  record ⨊ᵒᵖᵘ (F : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)) : 𝒰 ((𝑖 ⌄ 0) ⊔ (𝑗 ⌄ 0)) where
    constructor _,_
    field base : ⟨ 𝒞 ⟩
    field fib : ⟨ ⟨ F ⟩ base ⟩

  open ⨊ᵒᵖᵘ public

  module _ (F : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)) where
    macro
      ⨊ᵒᵖ = #structureOn (⨊ᵒᵖᵘ F)

  -- instance
  --   hasGrothendieckSumOp:𝐂𝐚𝐭 : hasGrothendieckSumOp (Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)) _
  --   hasGrothendieckSumOp:𝐂𝐚𝐭 = record { ⨊ᵒᵖ = ⨊ᵒᵖ }


  module _ {F : Functor (𝒞 ᵒᵖ) (𝐂𝐚𝐭 𝑗)} where
    private
      instance
        isCategory:F : ∀{b : ⟨ 𝒞 ⟩} -> isCategory (⟨ ⟨ F ⟩ b ⟩)
        isCategory:F {b} = of ⟨ F ⟩ b

      instance
        isSetoid:F : ∀{b : ⟨ 𝒞 ⟩} {x y : ⟨ ⟨ F ⟩ b ⟩} -> isSetoid (x ⟶ y)
        isSetoid:F {b} = isSetoid:Hom {{of ⟨ F ⟩ b}}

    record Hom-⨊ᵒᵖ (a b : ⨊ᵒᵖ F) : 𝒰 ((𝑖 ⌄ 1) ､ (𝑗 ⌄ 1)) where
      constructor _,_
      field base : base a ⟶ base b
      field fib : Hom (fib a) (⟨ map base ⟩ (fib b))

    open Hom-⨊ᵒᵖ public

    module _ {a b : ⨊ᵒᵖ F} where
      record _∼-Hom-⨊ᵒᵖ_ (f g : Hom-⨊ᵒᵖ a b) : 𝒰 (𝑖 ⌄ 2 ､ 𝑗 ⌄ 2) where
        constructor _,_
        field ∼-base : base f ∼ base g
        field ∼-fib : (fib f) ◆ (⟨ ⟨ cong-∼ ∼-base ⟩ ⟩ _) ∼ fib g


      instance
        isSetoid:Hom-⨊ᵒᵖ : isSetoid (Hom-⨊ᵒᵖ a b)
        isSetoid:Hom-⨊ᵒᵖ = setoid _∼-Hom-⨊ᵒᵖ_ {!!} {!!} {!!}



    instance
      isCategory:⨊ᵒᵖ : isCategory (⨊ᵒᵖ F)
      isCategory.Hom isCategory:⨊ᵒᵖ          = Hom-⨊ᵒᵖ
      isCategory.isSetoid:Hom isCategory:⨊ᵒᵖ = isSetoid:Hom-⨊ᵒᵖ
      isCategory.id isCategory:⨊ᵒᵖ           = {!!}
      isCategory._◆_ isCategory:⨊ᵒᵖ          = {!!}
      isCategory.unit-l-◆ isCategory:⨊ᵒᵖ     = {!!}
      isCategory.unit-r-◆ isCategory:⨊ᵒᵖ     = {!!}
      isCategory.unit-2-◆ isCategory:⨊ᵒᵖ     = {!!}
      isCategory.assoc-l-◆ isCategory:⨊ᵒᵖ    = {!!}
      isCategory.assoc-r-◆ isCategory:⨊ᵒᵖ    = {!!}
      isCategory._◈_ isCategory:⨊ᵒᵖ          = {!!}



