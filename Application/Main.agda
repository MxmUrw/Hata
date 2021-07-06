

module Application.Main where

open import Verification.Experimental.Conventions
open import Application.Definition
-- open import Verification.Experimental.Data.Real.Application.Definition

open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory

open import Verification.Experimental.Theory.Std.Generic.ProgrammingLanguage.Definition

-- testApp : Application
-- testApp = execute "test" (λ x -> PString (x <> x <> x))

-- getApplicationList : List (Application)
-- getApplicationList = testApp ∷ languageApplication (′ λC ′) ∷ []
-- getApplicationList = testApp ∷ realapp ∷ []

testApp : Executable Bool
testApp = executable false loop
  where
    loop : Event → Bool → List Reaction ×-H Bool
    loop (Event-ReadFile x) s = (Reaction-PrintDebug "hello!!!" ∷ Reaction-NewWindow ∷ Reaction-PrintDebug "Do you get this?" ∷ []) , true


getApplicationList : List RegisterExecutable
getApplicationList = registerExecutable "test" testApp ∷ []

{-# COMPILE GHC getApplicationList as getApplicationList #-}








