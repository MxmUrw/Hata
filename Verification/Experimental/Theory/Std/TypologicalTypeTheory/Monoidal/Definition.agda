
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.Monoidal.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ

instance
  isMonoidal:𝐓𝐲𝐩𝐞 : isMonoidal (𝐓𝐲𝐩𝐞 𝑖)
  isMonoidal:𝐓𝐲𝐩𝐞 = {!!}


record TypeTheory-⊗ (𝑗 : 𝔏) : 𝒰 (𝑗 ⁺ ⁺) where
  field 𝒯erm : CwJ (𝑗 , 𝑗 , 𝑗 , 𝑗)
  -- field {{Types}} : hasJudgements {𝑗 ⌄ 1} (𝐓𝐲𝐩𝐞 (𝑗 ⌄ 0))
  -- field typing : 𝒯erm ⟶ (𝐓𝐲𝐩𝐞 (𝑗 ⌄ 0))





