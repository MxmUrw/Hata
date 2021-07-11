

module Verification.Application.Main where

open import Verification.Experimental.Conventions
open import Verification.Application.Definition
open import Verification.Application.Render.Definition
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Data.Real.Application.Definition

open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory

open import Verification.Experimental.Theory.Std.Generic.ProgrammingLanguage.Definition

-- testApp : Application
-- testApp = execute "test" (λ x -> PString (x <> x <> x))

-- getApplicationList : List (Application)
-- getApplicationList = testApp ∷ languageApplication (′ λC ′) ∷ []
-- getApplicationList = testApp ∷ realapp ∷ []

renderTestApp : Bool → List Cairo.Cmd
renderTestApp _ =
    Cairo.doChangeState clearAll
  ∷ Cairo.doChangeState (set "a" (Cairo.string (Cairo.rgb 255 255 255) 15 "Hello world from Agda!!!!"))
  ∷ Cairo.doRender
    (λ get size →
       Cairo.item ((0 , 1) , (0 , 1)) (Cairo.rectangle (Cairo.rgb 31 31 31) size)
     ∷ Cairo.item ((20 , 1) , (20 , 1)) (Cairo.string (Cairo.rgb 255 255 255) 15 "Hello world from Agda!!!!")
     ∷ Cairo.item ((50 , 1) , (40 , 1)) (Cairo.string (Cairo.rgb 255 40 255) 30 "Do you see this?")
     ∷ [])
  ∷ []

testApp : Executable Bool
testApp = executable false loop
  where
    loop : Event → Bool → List (Reaction Bool) ×~ Bool
    loop (Event-ReadFile x) s = (Reaction-PrintDebug "hello!!! Yes! Do not regret" ∷ Reaction-NewWindow renderTestApp ∷ Reaction-PrintDebug "Do you get this?" ∷ []) , true


getApplicationList : List RegisterExecutable
getApplicationList = registerExecutable "test" testApp ∷ []

{-# COMPILE GHC getApplicationList as getApplicationList #-}








