
{-# OPTIONS --cubical --no-import-sorts #-}

module Verification.Conventions.Proprelude.Imports where

open import Agda.Primitive public using (lzero)
  renaming
  (Level to 𝔏; lsuc to _⁺ ; Setω to 𝒰ω ; Set to 𝒰' ; Prop to CompProp ; _⊔_ to join-𝔏 ;
  SSet to S𝒰
  )


open import Agda.Builtin.String public



-- these
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Bool public

-- overwrite the path type with something which compiles
module _ {𝑖 : 𝔏} {A : 𝒰' 𝑖} where
  _≡_ : A -> A -> 𝒰' 𝑖
  _≡_ a b = Bool -> A

PathP : ∀{𝑗} -> (B : Bool -> 𝒰' 𝑗) -> (B false) -> B true -> 𝒰' 𝑗
PathP B b0 b1 = (b : Bool) -> B b

I = Bool
i0 = false
i1 = true


-- copy the lifting
record Lift {i j} (A : 𝒰' i) : 𝒰' (join-𝔏 i j) where
  constructor lift
  field
    lower : A

open Lift public



open import Verification.Conventions.Proprelude.Replacement.Sum renaming (_⊎_ to _+-𝒰_ ; elim to elim-+-𝒰 ; inl to left ; inr to right ) hiding (map ; rec) public



