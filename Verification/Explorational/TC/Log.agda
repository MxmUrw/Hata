
module Verification.Core.Category.TC.Log where

open import Verification.Conventions
open import Verification.Core.Category.Definition

-- = A general definition of type theory.

-- | We are searching for a general, useful definition of the concept of a /type theory/.
--   An informal picture seems to be possible, where the rules of a TT generate a free "multicategory",
--   possibly subject to equations by reduction rules. The type annotations of this multicategory can
--   be forgotten, and give us the operad of untyped terms. The goal of the typechecker is to find out,
--   whether a given operadic terms is in the image of the forgetful functor |U : MC → Operad|.

-- | But, we are dealing here not quite with normal multicategories, but rather with /syndetic/ ones.
--   That is, those whose objects (types) consist of formal expressions, and thus are subject to unification
--   when terms are composed.

-- | Furthermore, additional features of the type theory seem to require different additional axiomatics of
--   our syndetic TC multicategories. For instance,
--   1. Polymorphism: Seems to require "horizontal meta-fication", i.e., the ability to speak about metavariables
--      in rules.
--   2. Dependent types: Seemingly a certain, different flavor of metafication. We mix metavariables with real variables.
--      Substitutions occur in (type-)terms. They do also in horizontal metafication, but here, in this case, we do not need formal sets of variables.
--      Further research necessary.
--   3. Subtyping: ?
--   4. Constraints: ?
--   5. typeclasses, relations: ?




