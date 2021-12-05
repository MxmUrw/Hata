
module Verification.Core.Category.Std.Fibration.Instance.BaseChange where

open import Verification.Core.Conventions

-- open import Verification.Core.Set.Setoid.Definition
-- open import Verification.Core.Set.Set.Definition
-- open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Category.Opposite
-- open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Category.Instance.Category
-- open import Verification.Core.Category.Std.Limit.Specific.Pullback

-- open import Verification.Core.Data.Universe.Definition
-- open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category


open import Verification.Core.Category.Std.Fibration.BaseChange.Definition
open import Verification.Core.Category.Std.Fibration.Definition


module _ {ℰ : Category 𝑖} {ℬ : Category 𝑗} (p : Fibration ℰ ℬ) where

  hasBaseChange:Fibration : hasBaseChange _ ℬ
  hasBaseChange:Fibration = basechange (FiberF p) {!!} {!!}



