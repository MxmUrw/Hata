
module Verification.Old.Core.Category.Natural where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Instance.Cat

private
  infixl 80 _◇_
  _◇_ = comp-Cat


-- % https://q.uiver.app/?q=WzAsNCxbMCwwLCIoRkcpWCJdLFswLDIsIkZYIl0sWzIsMCwiKFVGRylYIl0sWzIsMiwiKFVGKVgiXSxbMCwyLCJcXGJldGFfe0dYfSJdLFswLDEsIlxcYWxwaGFfWCIsMl0sWzIsMywiVVxcYWxwaGFfeCJdLFsxLDMsIlxcYmV0YV9YIiwyXV0=
-- | We want the following:
-- \[\begin{tikzcd}
-- 	{(FG)X} && {(UFG)X} \\
-- 	\\
-- 	FX && {(UF)X}
-- 	\arrow["{\beta_{GX}}", from=1-1, to=1-3]
-- 	\arrow["{\alpha_X}"', from=1-1, to=3-1]
-- 	\arrow["{U\alpha_x}", from=1-3, to=3-3]
-- 	\arrow["{\beta_X}"', from=3-1, to=3-3]
-- \end{tikzcd}\]

module _ {𝒞 𝒟 : Category 𝑖} where
  module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒞 𝒞} {U : Functor 𝒟 𝒟} where
    commutes-Nat : (α : G ◇ F ⟶ F) -> (β : F ⟶ F ◇ U) -> 𝒰 _
    commutes-Nat α β = ∀{x} -> ⟨ β ⟩ ◆ map ⟨ α ⟩ ≣ ⟨ α ⟩ {x} ◆ ⟨ β ⟩




