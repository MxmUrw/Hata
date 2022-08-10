
module Verification.Application.AgdaUI.Render.Definition where

open import Verification.Conventions
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.Rational.Definition
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Product.Definition

{-# FOREIGN GHC import Hata.Runtime.Application.Render.Definition #-}


data StateCmd (N : 𝒰₀) (X : 𝒰₀) : 𝒰₀ where
  clearAll : StateCmd N X
  clear : N -> StateCmd N X
  set : N -> X -> StateCmd N X

{-# COMPILE GHC StateCmd = data StateCmd (ClearAll | Clear | Set) #-}

record hasRenderer (N : 𝒰₀) (BaseItem Item : 𝒰₀) (DerivedInfo : 𝒰₀) (A : Monoid (ℓ₀ , ℓ₀)) : 𝒰₀ where
  field changeState : StateCmd N BaseItem -> ⟨ A ⟩
  field render : ((N -> Maybe DerivedInfo) -> Item) -> ⟨ A ⟩


--------------------------------------------------------------------
-- For Cairo

ℚ~ = (ℤ ×~ ℤ)

module Cairo where
  Extent : 𝒰₀
  Extent = ℚ~ ×~ ℚ~

  Location = ℚ~ ×~ ℚ~

  data RGB : 𝒰₀ where
    rgb : ℕ -> ℕ -> ℕ -> RGB

  {-# COMPILE GHC RGB = data RGB (RGB) #-}

  data BaseItem : 𝒰₀ where
    string : RGB -> ℕ -> String -> BaseItem
    rectangle : RGB -> Extent -> BaseItem

  {-# COMPILE GHC BaseItem = data BaseItem (StringBI | RectangleBI) #-}

  data Item : 𝒰₀ where
    item : Location -> BaseItem -> Item

  {-# COMPILE GHC Item = data Item (Item) #-}

  data Cmd : 𝒰₀ where
    doRender : ((String -> Maybe Extent) -> Extent -> List Item) -> Cmd
    doChangeState : StateCmd String BaseItem -> Cmd

  {-# COMPILE GHC Cmd = data Cmd (DoRender | DoChangeState) #-}




