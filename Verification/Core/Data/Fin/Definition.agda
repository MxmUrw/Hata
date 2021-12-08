
module Verification.Core.Data.Fin.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Prop.Subset
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
-- open import Verification.Core.Set.Finite.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder

-- open import Cubical.Data.Fin.Base renaming (elim to elim-Fin ; toℕ to toℕ-Fin) public

{-
macro
  𝔽 : ∀ n -> SomeStructure
  𝔽 n = #structureOn (Fin n)

macro
  𝔽ʳ : ∀ n -> SomeStructure
  𝔽ʳ n = #structureOn (Fin-R n)




module _ {n : ℕ} where
  instance
    isSetoid:Fin : isSetoid (𝔽 n)
    isSetoid:Fin = isSetoid:byPath
    -- isSetoid._∼'_ (isSetoid:Fin) = _≡_
    -- isSetoid.isEquivRel:∼ (isSetoid:Fin) = it

  instance
    isPreorder:Fin : isPreorder _ (𝔽 n)
    isPreorder._≤_ isPreorder:Fin (i , _) (j , _) = i ≤-ℕ j
    isPreorder.reflexive isPreorder:Fin = (0 , refl)
    isPreorder._⟡_ isPreorder:Fin = {!!}
    isPreorder.transp-≤ isPreorder:Fin = {!!}

  instance
    isPartialorder:Fin : isPartialorder (𝔽 n)
    isPartialorder.antisym isPartialorder:Fin = {!!}

  instance
    isTotalorder⁺:Fin : isTotalorder⁺ (𝔽 n)
    isTotalorder⁺.total⁺ isTotalorder⁺:Fin = {!!}

  instance
    isDiscrete':Fin : isDiscrete' (𝔽 n)
    is𝒫-Dec.decide-𝒫 (isDiscrete'.decidableEquality isDiscrete':Fin) = {!!}

  -- instance
  --   isFinite:Fin : isFinite (𝔽 n)
  --   isFinite:Fin = {!!}

-}
