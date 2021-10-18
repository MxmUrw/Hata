
module Verification.Application.Configuration.Static where

open import Verification.Conventions



data SupportedLanguage : 𝒰₀ where
  LambdaCalculusTypesᵗ : SupportedLanguage

instance
  IShow:SupportedLanguage : IShow SupportedLanguage
  IShow.show IShow:SupportedLanguage LambdaCalculusTypesᵗ = "LambdaCalculusTypes"

getSupportedLanguages : List SupportedLanguage
getSupportedLanguages = LambdaCalculusTypesᵗ ∷ []


-- getInferMap : SupportedLanguage -> ∑ λ (a : 𝐈𝐧𝐟𝐞𝐫) -> a ⟶ InferExpr
-- getInferMap = ?



