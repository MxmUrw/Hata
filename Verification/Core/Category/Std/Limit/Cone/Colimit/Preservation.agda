
module Verification.Core.Category.Std.Limit.Cone.Colimit.Preservation where

open import Verification.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2
-- open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
open import Verification.Core.Category.Std.Limit.Representation.Colimit.Definition



module _ {𝒞 : Category 𝑗} {𝒟 : Category 𝑖} (F : 𝐅𝐮𝐧𝐜 𝒞 𝒟) where
  preservesColimit : {𝒥 : Category 𝑘} (D : 𝐅𝐮𝐧𝐜 𝒥 𝒞) -> 𝒰 _
  preservesColimit D = ∀{x} -> isColimit D x -> isColimit (D ◆-𝐂𝐚𝐭 F) (⟨ F ⟩ x)

  preservesShapedColimits : (𝒥 : Category 𝑘) -> 𝒰 _
  preservesShapedColimits 𝒥 = ∀(D : 𝐅𝐮𝐧𝐜 𝒥 𝒞) -> preservesColimit D

  preservesAllColimits : (𝑘 : 𝔏 ^ 3) -> 𝒰 _
  preservesAllColimits 𝑘 = ∀{𝒥 : Category 𝑘} -> preservesShapedColimits 𝒥



