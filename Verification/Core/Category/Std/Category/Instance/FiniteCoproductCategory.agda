
module Verification.Core.Category.Std.Category.Instance.FiniteCoproductCategory where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
-- open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Lift.Definition
-- open import Verification.Core.Data.Fin.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Construction.Id
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Construction.Coproduct


module _ {𝒞 𝒟 : 𝐂𝐚𝐭 𝑖} where
  instance
    isCoproduct:+-𝐂𝐚𝐭 : isCoproduct 𝒞 𝒟 (𝒞 + 𝒟)
    isCoproduct.ι₀ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.ι₁ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.⦗ isCoproduct:+-𝐂𝐚𝐭 ⦘ = {!!}
    isCoproduct.reduce-ι₀ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.reduce-ι₁ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.expand-ι₀,ι₁ isCoproduct:+-𝐂𝐚𝐭 = {!!}
    isCoproduct.isSetoidHom:⦗⦘ isCoproduct:+-𝐂𝐚𝐭 = {!!}



