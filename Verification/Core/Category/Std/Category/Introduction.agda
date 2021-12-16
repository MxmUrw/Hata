
module Verification.Core.Category.Std.Category.Introduction where

-- | We introduce the notion of a category, and a few concepts which
--   are going to need, in particular coproducts and coequalizers.
--   All the theory in this chapter is standard, except for that fact
--   that we require the hom-types to have the additional structure
--   of a setoid. This has two motivations:
-- | - We can abstract over the actual notion of equality used
--     for a particular category.
-- | - The type inference of Agda sometimes gives better results
--     when the abstract definition of setoids is used, instead of the concrete
--     definition of equality. With our definition, when reasoning about
--     arrows in abstract categories, usually no additional annotations have to be
--     made regarding the objects involved.
-- |: The basic idea of this approach has been taken from a library for category
--    theory in Agda \cite{Agda:Cat:2021}. A standard reference for category theory
--    in general is \cite{saunders1971categories}.


