
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
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Type.Definition
open import Verification.Experimental.Data.Lift.Definition
open import Verification.Experimental.Algebra.Monoid.Definition

instance
  isMonoidal:𝐓𝐲𝐩𝐞 : isMonoidal (𝐓𝐲𝐩𝐞 𝑖)
  isMonoid._⋆_ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = _×-𝒰_
  isMonoid.◌ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = ⊤-𝒰
  isMonoid.unit-l-⋆ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = {!!}
  isMonoid.unit-r-⋆ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = {!!}
  isMonoid.assoc-l-⋆ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = {!!}
  isMonoid.assoc-r-⋆ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = {!!}
  isMonoid._`cong-⋆`_ (isMonoidal.isMonoid:this isMonoidal:𝐓𝐲𝐩𝐞) = {!!}

-- module _ {{Types : hasJudgements {_} (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))}} where
--   myTest : CwJ _
--   myTest = 𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺)


record TypeTheory-⊗ 𝑗 : 𝒰 (𝑗 ⁺ ⁺) where
  field 𝒯erm : CwJ _
  field {{Types}} : hasJudgements {𝑗 ⁺} (𝐓𝐲𝐩𝐞' 𝑗)
  field typing : 𝒯erm ⟶ (𝐓𝐲𝐩𝐞' 𝑗)

  -- field 𝒯erm : CwJ (𝑗 ⁺ , 𝑗 ⁺ , 𝑗 ⁺ , 𝑗 ⁺)
  -- field {{Types}} : hasJudgements {_} (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))
  -- field typing : 𝒯erm ⟶ (𝐓𝐲𝐩𝐞' (𝑗 , 𝑗 ⁺ , 𝑗 ⁺))





