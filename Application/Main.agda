

module Application.Main where

open import Verification.Experimental.Conventions
open import Application.Definition
-- open import Verification.Experimental.Data.Real.Application.Definition

open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory

open import Verification.Experimental.Theory.Std.ProgrammingLanguage.Definition

testApp : Application
testApp = execute "test" (λ x -> PString (x <> x <> x))

getApplicationList : List (Application)
getApplicationList = testApp ∷ languageApplication (′ λC ′) ∷ []
-- getApplicationList = testApp ∷ realapp ∷ []

{-# COMPILE GHC getApplicationList as getApplicationList #-}

