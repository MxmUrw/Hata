
module Verification.Application.AgdaUI.Applications.Editor.Definition where

open import Verification.Conventions
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Application.AgdaUI.Definition
open import Verification.Application.AgdaUI.Render.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Int.Instance.Monoid



record EditorState : 𝒰₀ where
  constructor testExe
  field textLoc : Cairo.Location

open EditorState

moveV : ℤ -> EditorState -> EditorState
moveV δ (testExe (a , (b , db))) = testExe (a , (b ⋆ δ , db))


renderTestApp : EditorState → List Cairo.Cmd
renderTestApp s =
    Cairo.doChangeState clearAll
  ∷ Cairo.doChangeState (set "a" (Cairo.string (Cairo.rgb 255 255 255) 15 "Hello world from Agda!!!!"))
  ∷ Cairo.doRender
    (λ get size →
       Cairo.item ((0 , 1) , (0 , 1)) (Cairo.rectangle (Cairo.rgb 31 31 31) size)
     ∷ Cairo.item ((20 , 1) , (20 , 1)) (Cairo.string (Cairo.rgb 255 255 255) 15 "Hello world from Agda!!!!")
     ∷ Cairo.item (textLoc s) (Cairo.string (Cairo.rgb 255 40 255) 30 "Do you see this?")
     ∷ [])
  ∷ []

editorExecutable : Executable EditorState
editorExecutable = executable (testExe ((0 , 1),(0 , 1))) loop
  where
    loop : Event → EditorState → List (Reaction EditorState) ×~ EditorState
    loop (Event-ReadFile x) s = (Reaction-PrintDebug "hello!!! Yes! Do not regret" ∷ Reaction-NewWindow renderTestApp ∷ Reaction-PrintDebug "Do you get this?" ∷ []) , s
    loop (Event-KeyPress key) s with key ≟ "j" | key ≟ "k"
    ... | true  | _     = Reaction-PrintDebug ">> Key down" ∷ [] , (moveV 10 s)
    ... | false | true  = Reaction-PrintDebug ">> Key up" ∷ [] , (moveV -10 s)
    ... | false | false = Reaction-PrintDebug ("Key " <> key) ∷ [] , s







