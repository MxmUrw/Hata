
module Verification.Experimental.Category.Std.Fibration.Instance.BaseChange where

open import Verification.Experimental.Conventions

-- open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Experimental.Set.Set.Definition
-- open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
-- open import Verification.Experimental.Category.Std.Category.Opposite
-- open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Category.Instance.Category
-- open import Verification.Experimental.Category.Std.Limit.Specific.Pullback

-- open import Verification.Experimental.Data.Universe.Definition
-- open import Verification.Experimental.Data.Universe.Everything


open import Verification.Experimental.Category.Std.Fibration.BaseChange.Definition
open import Verification.Experimental.Category.Std.Fibration.Definition


module _ {ℰ : Category 𝑖} {ℬ : Category 𝑗} (p : Fibration ℰ ℬ) where

  hasBaseChange:Fibration : hasBaseChange _ ℬ
  hasBaseChange:Fibration = basechange (FiberF p) {!!} {!!}



