
module Verification.Core.Data.List.Variant.Unary.DefinitionResult where
open import Verification.Conventions

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

-- | Such a presentation is automatically generated from the following source code:

