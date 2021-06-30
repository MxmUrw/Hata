
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
-- open import Verification.Experimental.Theory.Std.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition


instance
  isCategory:MetaTermCalculus : isCategory (ℓ₀ , ℓ₀) (MetaTermCalculus)
  isCategory.Hom' isCategory:MetaTermCalculus = {!!}
  isCategory.isSetoid:Hom isCategory:MetaTermCalculus = {!!}
  isCategory.id isCategory:MetaTermCalculus = {!!}
  isCategory._◆_ isCategory:MetaTermCalculus = {!!}
  isCategory.unit-l-◆ isCategory:MetaTermCalculus = {!!}
  isCategory.unit-r-◆ isCategory:MetaTermCalculus = {!!}
  isCategory.unit-2-◆ isCategory:MetaTermCalculus = {!!}
  isCategory.assoc-l-◆ isCategory:MetaTermCalculus = {!!}
  isCategory.assoc-r-◆ isCategory:MetaTermCalculus = {!!}
  isCategory._◈_ isCategory:MetaTermCalculus = {!!}

macro
  𝐌𝐓𝐂 = #structureOn MetaTermCalculus


instance
  isLogicalFramework:MetaTermCalculus : isLogicalFramework (𝐌𝐨𝐧𝐂𝐚𝐭 _) 𝐌𝐓𝐂
  isLogicalFramework.Free isLogicalFramework:MetaTermCalculus = ?
  isLogicalFramework.Forget isLogicalFramework:MetaTermCalculus = ?
  isLogicalFramework.isFunctor:Free isLogicalFramework:MetaTermCalculus = ?
  isLogicalFramework.isFunctor:Forget isLogicalFramework:MetaTermCalculus = ?
  isLogicalFramework.⟦ isLogicalFramework:MetaTermCalculus ⟧ = ?




