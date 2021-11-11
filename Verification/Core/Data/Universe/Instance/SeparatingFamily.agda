
module Verification.Core.Data.Universe.Instance.SeparatingFamily where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Core.Data.Universe.Instance.Category


private
  sep : ∀ 𝑗 -> ∀{𝑖} -> ⊤-𝒰 {𝑗} -> 𝒰 𝑖
  sep _ = const ⊤-𝒰

instance
  isSeparatingFamily:const⊤ : isSeparatingFamily (𝐔𝐧𝐢𝐯 𝑖) (sep 𝑗)
  isSeparatingFamily.separate isSeparatingFamily:const⊤ ϕ ψ x = P
    where
      P : ϕ ∼ ψ
      P = λ i a → x {tt} (const a) i tt

module _ {𝑖} {𝑗} where
  instance
    hasSeparatingFamily:𝐔𝐧𝐢𝐯 : hasSeparatingFamily 𝑗 (𝐔𝐧𝐢𝐯 𝑖)
    hasSeparatingFamily:𝐔𝐧𝐢𝐯 = record
                                { separator = sep 𝑗
                                ; isSeparatingFamily:seperators = it
                                }



