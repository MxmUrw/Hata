
module Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Natural.Instance.Category

record hasGrothendieckSum (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field ⨊ : A -> B

open hasGrothendieckSum {{...}} public

module _ {𝒞 : Category 𝑖} where


  record ⨊-𝐂𝐚𝐭 (F : Functor 𝒞 (𝐂𝐚𝐭 𝑗)) : 𝒰 ((𝑖 ⌄ 0) ⊔ (𝑗 ⌄ 0)) where
    constructor _,_
    field bas : ⟨ 𝒞 ⟩
    field fib : ⟨ ⟨ F ⟩ bas ⟩

  open ⨊-𝐂𝐚𝐭 public using (bas ; fib)
  -- open ⨊-𝐂𝐚𝐭 {{...}} public using (fib)

  instance
    hasGrothendieckSum:𝐂𝐚𝐭 : hasGrothendieckSum (Functor 𝒞 (𝐂𝐚𝐭 𝑗)) _
    hasGrothendieckSum:𝐂𝐚𝐭 = record { ⨊ = ⨊-𝐂𝐚𝐭 }


  module _ {F : Functor 𝒞 (𝐂𝐚𝐭 𝑗)} where
    private
      instance
        isCategory:F : ∀{b : ⟨ 𝒞 ⟩} -> isCategory (⟨ ⟨ F ⟩ b ⟩)
        isCategory:F {b} = of ⟨ F ⟩ b

      instance
        isSetoid:F : ∀{b : ⟨ 𝒞 ⟩} {x y : ⟨ ⟨ F ⟩ b ⟩} -> isSetoid (x ⟶ y)
        isSetoid:F {b} = isSetoid:Hom {{of ⟨ F ⟩ b}}

    record Hom-⨊-𝐂𝐚𝐭 (a b : ⨊ F) : 𝒰 ((𝑖 ⌄ 1) ､ (𝑗 ⌄ 1)) where
      constructor _,_
      field bas : bas a ⟶ bas b
      field fib : Hom (⟨ map bas ⟩ (fib a)) (fib b)

    open Hom-⨊-𝐂𝐚𝐭 public

    module _ {a b : ⨊ F} where
      record _∼-Hom-⨊-𝐂𝐚𝐭_ (f g : Hom-⨊-𝐂𝐚𝐭 a b) : 𝒰 (𝑖 ⌄ 2 ､ 𝑗 ⌄ 2) where
        constructor _,_
        field ∼-bas : bas f ∼ bas g
        field ∼-fib : fib f ∼ ⟨ ⟨ cong-∼ ∼-bas ⟩ ⟩ {_} ◆ fib g

      instance
        isSetoid:Hom-⨊-𝐂𝐚𝐭 : isSetoid (Hom-⨊-𝐂𝐚𝐭 a b)
        isSetoid:Hom-⨊-𝐂𝐚𝐭 = setoid _∼-Hom-⨊-𝐂𝐚𝐭_ {!!} {!!} {!!}


    instance
      isCategory:⨊-𝐂𝐚𝐭 : isCategory (⨊-𝐂𝐚𝐭 F)
      isCategory.Hom isCategory:⨊-𝐂𝐚𝐭          = Hom-⨊-𝐂𝐚𝐭
      isCategory.isSetoid:Hom isCategory:⨊-𝐂𝐚𝐭 = isSetoid:Hom-⨊-𝐂𝐚𝐭
      isCategory.id isCategory:⨊-𝐂𝐚𝐭           = {!!}
      isCategory._◆_ isCategory:⨊-𝐂𝐚𝐭          = {!!}
      isCategory.unit-l-◆ isCategory:⨊-𝐂𝐚𝐭     = {!!}
      isCategory.unit-r-◆ isCategory:⨊-𝐂𝐚𝐭     = {!!}
      isCategory.unit-2-◆ isCategory:⨊-𝐂𝐚𝐭     = {!!}
      isCategory.assoc-l-◆ isCategory:⨊-𝐂𝐚𝐭    = {!!}
      isCategory.assoc-r-◆ isCategory:⨊-𝐂𝐚𝐭    = {!!}
      isCategory._◈_ isCategory:⨊-𝐂𝐚𝐭          = {!!}





