
module Verification.Experimental.Category.Std.Category.Subcategory.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition


record isSubcategory (𝒞 : Category 𝑖) {𝑘 : 𝔏} (A : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺) where
  field subcat : A -> ⟨ 𝒞 ⟩
  field isHom-subcat : ∀{a b} -> subcat a ⟶ subcat b -> 𝒰 𝑘
  field isHom-subcat:id : ∀{a} -> isHom-subcat (id {a = subcat a})


-- module _ (𝒞 : Category 𝑖) where
  -- record Subcategory {A : 𝒰 𝑗} (ι : A -> ⟨ 𝒞 ⟩) (P : ∀{a b} -> ι a ⟶ ι b -> 𝒰 𝑘) : 𝒰 (𝑖 ⌄ 0) where



