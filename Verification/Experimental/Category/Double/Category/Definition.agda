
module Verification.Core.Category.Double.Category.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition

record isDoubleCategory {𝑗} {𝑘} {𝑖} (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺) ､ (𝑘 ⁺)) where
  field Vertical : Category 𝑗
  field VerticalObj : ⟨ 𝒞 ⟩ -> ⟨ Vertical ⟩
  field 2Cell : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) (g : c ⟶ d) (v : VerticalObj a ⟶ VerticalObj c) (w : VerticalObj b ⟶ VerticalObj d)
                -> 𝒰 𝑘

module _ (𝑖 : 𝔏 ^ 7) where
  DoubleCategory = (Category (𝑖 ⌄ 0 ⋯ 2)) :& isDoubleCategory {𝑖 ⌄ 3 ⋯ 5} {𝑖 ⌄ 6}

  macro
    𝐃𝐨𝐮𝐛𝐥𝐞𝐂𝐚𝐭 = #structureOn DoubleCategory






