
module Verification.Core.Theory.Std.Specific.ProductTheory.Module where

open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Definition public
    hiding (分Term ; 全Term ; 𝒜)

module 𝕋× where
  module 統 where
    open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.PCF public
    open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Instance.FormalSystem public
    open import Verification.Core.Theory.Std.Specific.ProductTheory.Variant.Unification.Definition public
      using (分Term ; 全Term ; 𝒜)


  -- renaming (𝒜 to 𝕋×؛統؛𝒜)
      -- using (分Term ; 全Term ; 𝒜)

-- open 𝕋×.統 public
--   hiding (分Term ; 全Term ; 𝒜 ; ProductTheory)


