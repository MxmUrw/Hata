
module Verification.Core.Category.Std.Category.Construction.BaseChange where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.CategoryLike
open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Category.Construction.Id
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
-- open import Verification.Core.Category.Std.Morphism.Iso

module _ {𝑖𝑖₀ : 𝔏} where
  𝑖𝑖 : 𝔏 ^ 3
  𝑖𝑖 = 𝑖𝑖₀ , 𝑖𝑖₀ , 𝑖𝑖₀
  module _ {𝒞 : Category 𝑖𝑖} {𝒟 : Category 𝑖𝑖} where

    module _ (f : Functor 𝒞 𝒟) where
      -- pbᵘ : (𝐅𝐮𝐧𝐜 𝒟 (𝐂𝐚𝐭 𝑘)) -> (𝐅𝐮𝐧𝐜 𝒞 (𝐂𝐚𝐭 𝑘))
      -- pbᵘ F = f ◆-𝐂𝐚𝐭 F

      -- pb : Functor (𝐅𝐮𝐧𝐜 𝒟 (𝐂𝐚𝐭 𝑘)) (𝐅𝐮𝐧𝐜 𝒞 (𝐂𝐚𝐭 𝑘))
      -- pb = pbᵘ since {!!}


      module _ (F : 𝐅𝐮𝐧𝐜 𝒞 (𝐂𝐚𝐭 𝑖𝑖)) where

        record C∑ᵘ (d : ⟨ 𝒟 ⟩) : 𝒰 (𝑖𝑖) where
          constructor _at_,_
          field pt : ⟨ 𝒞 ⟩
          field fst : ⟨ ⟨ F ⟩ pt ⟩
          field snd : ⟨ f ⟩ pt ⟶ d

        open C∑ᵘ public

        module _ (d : ⟨ 𝒟 ⟩) where
          macro C∑ = #structureOn (C∑ᵘ d)

        module _ {d : ⟨ 𝒟 ⟩} where

          record Hom-C∑ (a b : C∑ d) : 𝒰 𝑖𝑖 where
            constructor _at_,_
            field ptmap : pt a ⟶ pt b
            field fst : Hom {{of ⟨ F ⟩ (pt b)}} (⟨ map ptmap ⟩ (fst a)) (fst b)
            field snd : map ptmap ◆ snd b ∼ snd a

          open Hom-C∑ public

          id-C∑ : ∀{a : C∑ d} -> Hom-C∑ a a
          id-C∑ {a} = id at fst' , {!!}
            where
              -- open isCategory (of (⟨ F ⟩ (pt a)))
              ida : Hom {{of (⟨ F ⟩ (pt a))}} (fst a) (fst a)
              ida = id {{of (⟨ F ⟩ (pt a))}}
                -- where open isCategory (of (⟨ F ⟩ (pt a)))

              -- p0 : ∀ x -> ⟨ mapOf F (id {a = pt a}) ⟩ x ≅ x
              -- p0 x = {!⟨ functoriality-id {{of F}}!}

              fst' : Hom {{of ⟨ F ⟩ (pt a)}} (⟨ map id ⟩ (fst a)) (fst a)
              fst' = {!!}

          -- Hom-C∑ : C∑ d -> C∑ d -> 𝒰 𝑖𝑖
          -- Hom-C∑ = {!!}

          instance
            isCategory:C∑ : isCategory (C∑ d)
            isCategory.Hom isCategory:C∑ = {!!}
            isCategory.isSetoid:Hom isCategory:C∑ = {!!}
            isCategory.id isCategory:C∑ = {!!}
            isCategory._◆_ isCategory:C∑ = {!!}
            isCategory.unit-l-◆ isCategory:C∑ = {!!}
            isCategory.unit-r-◆ isCategory:C∑ = {!!}
            isCategory.unit-2-◆ isCategory:C∑ = {!!}
            isCategory.assoc-l-◆ isCategory:C∑ = {!!}
            isCategory.assoc-r-◆ isCategory:C∑ = {!!}
            isCategory._◈_ isCategory:C∑ = {!!}


        F∑ : 𝐅𝐮𝐧𝐜 𝒟 (𝐂𝐚𝐭 𝑘)
        F∑ = {!!}



