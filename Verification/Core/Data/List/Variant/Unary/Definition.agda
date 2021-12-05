
module Verification.Core.Data.List.Variant.Unary.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete



--------------------------------------------------------------------
-- [Definition]
-- (NOTE: Lists are actually defined in Agda.Builtin.List,
--        we merely reproduce the definition here for introduction
--        purposes.)
--
private
  -- | For any type |A|, lists with elements of type |A| are defined
  --   as the data type [..] with two constructors.
  data List' (A : 𝒰 𝑖) : 𝒰 𝑖 where

  -- | - The constructor [..], which denotes the empty list.
    []  : List' A

  -- | - The constructor [..], which denotes the operation
  --     of prepending an element |a| to a list |as|,
  --     resulting in the larger list |a ∷ as|.
    _∷_ : A -> List' A → List' A

-- #Notation/Rewrite# List' = List
-- //



--------------------------------------------------------------------
-- [Hide]
-- Some proofs which should be moved somewhere else.
module _ {A : 𝒰 𝑖} where
  module _ {{_ : isDiscrete A}} where
    private
      lem-1 : (a b : List A) → Decision (a ≡-Str b)
      lem-1 [] [] = yes refl-≣
      lem-1 [] (x ∷ b) = no λ ()
      lem-1 (x ∷ a) [] = no λ ()
      lem-1 (x ∷ a) (y ∷ b) with x ≟-Str y | lem-1 a b
      ... | yes p | yes q = yes (cong₂-Str _∷_ p q)
      ... | yes p | no ¬p = no λ {refl-≣ → ¬p refl-≣}
      ... | no ¬p | Y = no λ {refl-≣ → ¬p refl-≣}

    instance
      isDiscrete:List : isDiscrete (List A)
      isDiscrete:List = record { _≟-Str_ = lem-1 }

  instance
    isSet-Str:List : {{_ : isSet-Str A}} -> isSet-Str (List A)
    isSet-Str:List = {!!}


module _ {A : 𝒰 𝑖} where
  instance
    isSetoid:List : isSetoid (List A)
    isSetoid:List = isSetoid:byId
-- //

--------------------------------------------------------------------
-- [Hide]
-- | We provide patterns for using lists with a few elements

pattern ⦋⦌ = []
-- pattern ⦋_⦌ a = a ∷ []
pattern ⦋_،_⦌ a b = a ∷ b ∷ []
pattern ⦋_،_،_⦌ a b c = a ∷ b ∷ c ∷ []
pattern ⦋_،_،_،_⦌ a b c d = a ∷ b ∷ c ∷ d ∷ []
pattern ⦋_،_،_،_،_⦌ a b c d e = a ∷ b ∷ c ∷ d ∷ e ∷ []

-- //
