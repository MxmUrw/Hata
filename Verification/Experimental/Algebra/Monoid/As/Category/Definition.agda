
module Verification.Core.Algebra.Monoid.As.Category.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Algebra.Monoid.Definition

-- record
-- { Hom' = ?
-- ; isSetoid:Hom = ?
-- ; id = ?
-- ; _◆_ = ?
-- ; unit-l-◆   = ?
-- ; unit-r-◆   = ?
-- ; unit-2-◆   = ?
-- ; assoc-l-◆  = ?
-- ; assoc-r-◆  = ?
-- ; _◈_        = ?
-- }



module _ (M : Monoid 𝑖) where
  record DeloopingCat : 𝒰 𝑖 where

  𝐃𝐞𝐥𝐨𝐨𝐩𝐢𝐧𝐠𝐂𝐚𝐭 : SomeStructure
  𝐃𝐞𝐥𝐨𝐨𝐩𝐢𝐧𝐠𝐂𝐚𝐭 = structureOn DeloopingCat

module _ {M : Monoid 𝑖} where
  instance
    isCategory:DeloopingCat : isCategory 𝑖 (𝐃𝐞𝐥𝐨𝐨𝐩𝐢𝐧𝐠𝐂𝐚𝐭 M)
    isCategory:DeloopingCat =
      record
      { Hom'         = λ _ _ -> ⟨ M ⟩
      ; isSetoid:Hom = isSetoid:Hom-Base
      ; id           = incl ◌
      ; _◆_          = λ f g -> incl (⟨ f ⟩ ⋆ ⟨ g ⟩)
      ; unit-l-◆     = incl ⟨ unit-l-⋆ ⟩
      ; unit-r-◆     = incl ⟨ unit-r-⋆ ⟩
      ; unit-2-◆     = incl ⟨ unit-l-⋆ ⟩
      ; assoc-l-◆    = incl ⟨ assoc-l-⋆ ⟩
      ; assoc-r-◆    = incl ⟨ assoc-r-⋆ ⟩
      ; _◈_          = λ p q -> incl ⟨ incl ⟨ p ⟩ ≀⋆≀ incl ⟨ q ⟩ ⟩
      }



-- 𝜂 η α β
-- 𝛢 	𝛣 	𝛤 	𝛥 	𝛦 	𝛧 	𝛨 	𝛩 	𝛪 	𝛫 	𝛬 	𝛭 	𝛮 	𝛯
-- U+1D6Fx 	𝛰 	𝛱 	𝛲 	𝛳 	𝛴 	𝛵 	𝛶 	𝛷 	𝛸 	𝛹 	𝛺 	𝛻 	𝛼 	𝛽 	𝛾 	𝛿
-- U+1D70x 	𝜀 	𝜁 	𝜂 	𝜃 	𝜄 	𝜅 	𝜆 	𝜇 	𝜈 	𝜉 	𝜊 	𝜋 	𝜌 	𝜍 	𝜎 	𝜏
-- U+1D71x 	𝜐 	𝜑 	𝜒 	𝜓 	𝜔 	𝜕 	𝜖 	𝜗 	𝜘 	𝜙 	𝜚 	𝜛



