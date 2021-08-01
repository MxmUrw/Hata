
module Verification.Experimental.Set.Setoid.Codiscrete where

open import Verification.Conventions
-- open import Verification.Experimental.Data.Prop.Definition
-- open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Experimental.Category.Std.Category.Definition


isSetoid:byCodiscrete : ∀{A : 𝒰 𝑖} -> isSetoid {𝑗} A
isSetoid._∼_ isSetoid:byCodiscrete  = λ _ _ -> ⊤-𝒰
isSetoid.refl isSetoid:byCodiscrete = tt
isSetoid.sym isSetoid:byCodiscrete  = λ x₁ → tt
isSetoid._∙_ isSetoid:byCodiscrete  = λ x₁ x₂ → tt



