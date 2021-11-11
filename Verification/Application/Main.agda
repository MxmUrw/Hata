

module Verification.Application.Main where

open import Verification.Conventions
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Application.Definition
open import Verification.Application.Render.Definition
open import Verification.Core.Data.Product.Definition
-- open import Verification.Core.Data.Rational.Definition
open import Verification.Core.Data.Int.Definition


open import Verification.Application.Applications.InferStandalone.Definition
open import Verification.Application.Applications.Editor.Definition
open import Verification.Application.Applications.Test.Definition

-- open import Verification.Core.Data.Real.Application.Definition

-- open import Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory

-- open import Verification.Core.Theory.Std.Generic.ProgrammingLanguage.Definition
-- open import Verification.Core.Theory.Std.Specific.ProductClosedTheory.Inference.Definition

-- testApp : Application
-- testApp = execute "test" (λ x -> PString (x <> x <> x))

-- getApplicationList : List (Application)
-- getApplicationList = testApp ∷ languageApplication (′ λC ′) ∷ []
-- getApplicationList = testApp ∷ realapp ∷ []



record PrintExe : 𝒰₀ where
  constructor printExe

instance
  IShow:Bool : IShow Bool
  IShow.show IShow:Bool false = "false"
  IShow.show IShow:Bool true = "true"

printApp : Executable PrintExe
printApp = executable (printExe) loop
  where
    loop : Event → PrintExe → List (Reaction PrintExe) ×~ PrintExe
    loop (Event-ReadFile f) s = Reaction-PrintDebug "not implemented" ∷ [] , s
    -- (Reaction-PrintDebug (show (compareLambdaType f)) ∷ []) , s
    loop _ s = Reaction-PrintDebug "not implemented" ∷ [] , s



getApplicationList : List RegisterExecutable
getApplicationList = registerExecutable "infer" inferStandaloneExecutable
                     ∷ registerExecutable "editor" editorExecutable
                     ∷ registerExecutable "test" testExecutable
                     ∷ []

{-# COMPILE GHC getApplicationList as getApplicationList #-}







