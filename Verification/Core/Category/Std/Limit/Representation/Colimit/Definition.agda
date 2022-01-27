
module Verification.Core.Category.Std.Limit.Representation.Colimit.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.2Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Variant.Binary
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid
open import Verification.Core.Category.Std.Functor.Representable2



module _ (𝒥 : Category 𝑘) {𝒞 : Category 𝑙} where

  Coconst : 𝐅𝐮𝐧𝐜 𝒞 (𝐅𝐮𝐧𝐜 𝒥 𝒞 ᵒᵖ)
  Coconst = (λ x -> const x since isFunctor:const) since {!!}

  Const' : 𝐅𝐮𝐧𝐜 (𝒞 ᵒᵖ) (𝐅𝐮𝐧𝐜 𝒥 𝒞 ᵒᵖ)
  Const' = {!!}

  Const'' : 𝐅𝐮𝐧𝐜 (𝒞) (𝐅𝐮𝐧𝐜 𝒥 𝒞)
  Const'' = Const since isFunctor:Const

  module _ (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) where
    F2 : 𝐅𝐮𝐧𝐜 (𝐅𝐮𝐧𝐜 𝒥 𝒞 ᵒᵖ) (𝐒𝐭𝐝 _)
    F2 = ℎ𝑜𝑚 F

module _ {𝒥 : Category 𝑖} {𝒞 : Category 𝑗} where

  isLimit : (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) -> ⟨ 𝒞 ⟩ -> 𝒰 _
  isLimit F x = isRepresented (Const' 𝒥 ◆-𝐂𝐚𝐭 ℎ𝑜𝑚 F) x

  isColimit : (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) -> ⟨ 𝒞 ⟩ -> 𝒰 _
  isColimit F x = isCorepresented (Const'' 𝒥 ◆-𝐂𝐚𝐭 ℎ𝑜𝑚ᵒᵖ F) x

  -- hasColimit : (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) -> 𝒰 _
  -- hasColimit F = ∑ λ (x : ⟨ 𝒞 ⟩) -> isCorepresented (Coconst ◆-𝐂𝐚𝐭 ℎ𝑜𝑚 F) x

--
-- we show that these colimits are the same as the ones
-- defined by cones
--

  open import Verification.Core.Category.Std.Limit.Cone.Colimit.Definition
    renaming (isColimit to isConeColimit)

  open import Verification.Core.Category.Std.Limit.Cone.Limit.Definition
    renaming (isLimit to isConeLimit)

  module _ (F : 𝐅𝐮𝐧𝐜 𝒥 𝒞) (x : ⟨ 𝒞 ⟩) where
    prop-1 : isLimit F x -> isConeLimit F x
    prop-1 P =
      let ϕ : (Const' 𝒥 ◆-𝐂𝐚𝐭 ℎ𝑜𝑚 F) ≅-Co𝐏𝐒𝐡 ℎ𝑜𝑚 x
          ϕ = rep P

          αᵘ : ∀(j : ⟨ 𝒥 ⟩) -> x ⟶ ⟨ F ⟩ j
          αᵘ j = let f = ⟨ inverse-◆-Co𝐏𝐒𝐡 (of ϕ) ⟩ (x)
                 in {!!} -- ⟨ ⟨ f ⟩ id ⟩ j
                 -- ⟨ f ⟩ ({!!} since {!!})
                  -- ⟨ ⟨ ϕ ⟩ (⟨ F ⟩ j) ⟩ ?

      in record
        { limitCocone = {!!}
        ; limitUniversal = {!!}
        }
{-
-}



