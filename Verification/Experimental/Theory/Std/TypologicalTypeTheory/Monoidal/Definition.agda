
module Verification.Experimental.Theory.Std.TypologicalTypeTheory.Monoidal.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Type.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Algebra.Monoid.Definition

-- module _ {{Types : hasJudgements {_} (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))}} where
--   myTest : CwJ _
--   myTest = 𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺)


module _ (K : Kinding 𝑖) where
  record TypeTheory-⊗ 𝑗 : 𝒰 (𝑖 ､ 𝑗 ⁺ ⁺) where
    field 𝒯erm : CwJ K _
    field {{Types}} : isCwJ K (𝐓𝐲𝐩𝐞' 𝑗)
    field typing : 𝒯erm ⟶ (𝐓𝐲𝐩𝐞' 𝑗)

  -- field 𝒯erm : CwJ (𝑗 ⁺ , 𝑗 ⁺ , 𝑗 ⁺ , 𝑗 ⁺)
  -- field {{Types}} : hasJudgements {_} (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))
  -- field typing : 𝒯erm ⟶ (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))





