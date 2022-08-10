
module Verification.Application.AgdaUI.Editor.Notes where

open import Verification.Conventions


-- | The editing experience is defined by multiple layers:
-- | - /char layer/. One cursor is always on this layer. Whenever one drops down here,
--                   one will be at the position of the cursor.
--                   But, there is a second, "area"-cursor, which can move between the other layers.
--                   That one decides what part of the code we are editing.
-- | - /token layer/
-- | - /prettified tokens/?
-- | - /AST/


-- |: The "current" layer defines which area cursor is being used. If one is on the AST then one
--    is on "main" branching points, i.e., e.g. on parenthesised blocks.

-- | Editing happens by selecting an AST node as edit-target. This node is then added to the
--   list of current goals, with its boundary informations, and dropped from the AST. Then after editing it
--   this part is parsed back into AST and typechecked.

-- ====* Questions
-- | - How does the interface to Haskell look? We want to have an Agda model of the rendering space,
--     and only re-render things which actually changed.













