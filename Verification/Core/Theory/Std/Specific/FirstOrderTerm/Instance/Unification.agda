
{-# OPTIONS --experimental-lossy-unification #-}
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Unification where

open import Verification.Conventions hiding (_โ_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Base
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Main
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Size

open import Verification.Core.Computation.Unification.Categorical.PrincipalFamilyCat


module _ {๐ : ๐ฏFOSignature ๐} where

  -- postulate
  --   instance
  --     hasUnification:๐ฏโterm : hasUnification (โง๐๐ฎ๐๐ฌ๐ญ (๐ฏโterm ๐))

  instance
    isPrincipalFamilyCat:๐๐ญ๐ฑ-๐ร : isPrincipalFamilyCat (โง๐๐ฎ๐๐ฌ๐ญ (๐ฏโterm ๐))
    isPrincipalFamilyCat:๐๐ญ๐ฑ-๐ร = record { isBase = isBase-๐ร ; โC = โ-๐ร ; isPrincipalC:Base = decide-Base-๐ร }

  abstract
    instance
      hasUnification:๐๐ญ๐ฑ-๐ร : hasUnification (โง๐๐ฎ๐๐ฌ๐ญ (๐ฏโterm ๐))
      hasUnification:๐๐ญ๐ฑ-๐ร = hasUnification:byPrincipalFamilyCat

