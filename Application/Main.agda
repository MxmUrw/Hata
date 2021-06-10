

module Application.Main where

open import Verification.Experimental.Conventions
open import Application.Definition
open import Verification.Experimental.Data.Real.Application.Definition

testApp : Application
testApp = execute "test" (λ x -> PString (x <> x <> x))

getApplicationList : List (Application)
getApplicationList = testApp ∷ realapp ∷ []

{-# COMPILE GHC getApplicationList as getApplicationList #-}

