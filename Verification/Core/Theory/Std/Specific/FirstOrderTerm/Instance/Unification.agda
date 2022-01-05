
{-# OPTIONS --experimental-lossy-unification #-}
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Unification where

open import Verification.Conventions hiding (_⊔_)

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


module _ {𝓅 : 𝒯FOSignature 𝑖} where

  -- postulate
  --   instance
  --     hasUnification:𝒯⊔term : hasUnification (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term 𝓅))

  instance
    isPrincipalFamilyCat:𝐂𝐭𝐱-𝕋× : isPrincipalFamilyCat (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term 𝓅))
    isPrincipalFamilyCat:𝐂𝐭𝐱-𝕋× = record { isBase = isBase-𝕋× ; ∂C = ∂-𝕋× ; isPrincipalC:Base = decide-Base-𝕋× }

  abstract
    instance
      hasUnification:𝐂𝐭𝐱-𝕋× : hasUnification (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term 𝓅))
      hasUnification:𝐂𝐭𝐱-𝕋× = hasUnification:byPrincipalFamilyCat

