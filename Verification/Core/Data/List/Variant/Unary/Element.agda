
module Verification.Core.Data.List.Variant.Unary.Element where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Data.List.Variant.Binary.Natural

open import Verification.Core.Data.List.Variant.Unary.Definition


-- | Having defined lists, we want to speak about elements
--   of lists, that is, we want a proposition |as ∍ a|,
--   that the list |as| contains the element |a|.
--   In fact, since lists might contain the same element
--   at multiple positions, it is useful to include this information
--   and have |as ∍ a| not be a mere proposition, but to be the
--   set of all occurences of |a| inside of |as|.

-- [Definition]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where

  -- |> The data type [..] is inhabited by elements
  --   describing the occurrences of |a| in |as|.
  data _∍♮_ : List A -> A -> 𝒰 𝑖 where

  -- |> It is defined using two constructors

  -- | - Given any list |bs|, we can conclude that
  --     the list |a ∷ bs| contains the element |a|.
    incl : ∀{a bs} -> (a ∷ bs) ∍♮ a

  -- | - Furthermore, if we know that some list |bs|
  --     already contains |a|, then after prepending any
  --     element |b| to that list, it still contains |a|.
    skip : ∀{a b bs} -> bs ∍♮ a -> (b ∷ bs) ∍♮ a

  -- |: Thus, every occurence of |a| in |as| corresponds
  --    to a proof |as ∍♮ a|, given by a sequence of |skip|
  --    constructors followed by |incl| when that occurence is reached.

-- #Notation/Rewrite# ∍♮ = ∍
-- //


