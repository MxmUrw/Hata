
module Verification.Core.Set.Setoid.Discrete where

open import Verification.Conventions
-- open import Verification.Core.Data.Prop.Definition
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Set.Setoid.Definition


isSetoid:byDiscrete : ∀{A : 𝒰 𝑖} -> isSetoid {𝑖} A
isSetoid._∼_ isSetoid:byDiscrete = _≡_
isSetoid.refl isSetoid:byDiscrete = refl-≡
isSetoid.sym isSetoid:byDiscrete = sym-Path
isSetoid._∙_ isSetoid:byDiscrete = _∙-≡_

module _ {A : 𝒰 𝑖}
         {B : 𝒰 𝑘} {{_ : isSetoid {𝑙} B}}
         where

  isSetoidHom:byDiscrete : {f : A -> B} -> isSetoidHom (A since isSetoid:byDiscrete) ′ B ′ f
  isSetoidHom:byDiscrete {f} = record { cong-∼ = λ p → ≡→∼ (cong f p) }





