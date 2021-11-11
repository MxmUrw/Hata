
module Verification.Core.Set.Setoid.Discrete where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Definition
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Set.Setoid.Definition


isSetoid:byDiscrete : ∀{A : 𝒰 𝑖} -> isSetoid {𝑖} A
isSetoid._∼_ isSetoid:byDiscrete = _≣_
isSetoid.refl isSetoid:byDiscrete = refl-≣
isSetoid.sym isSetoid:byDiscrete = sym-≣
isSetoid._∙_ isSetoid:byDiscrete = _∙-≣_







