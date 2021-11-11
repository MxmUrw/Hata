
module Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.EpiMono where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Core.Set.Setoid
-- open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.Mono.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity

open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition


module _ {𝒞 : Category 𝑖} where
  module _ {a b x : ⟨ 𝒞 ⟩} {{_ : isCoproduct a b x}} where

    mono-ι₀ : isMono ι₀
    mono-ι₀ = {!!}


