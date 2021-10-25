
module Verification.Application.Configuration.Static where

open import Verification.Conventions

open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.Task


data SupportedLanguage : 𝒰₀ where
  LambdaCalculusTypesᵗ : SupportedLanguage
  Testᵗ : SupportedLanguage

instance
  IShow:SupportedLanguage : IShow SupportedLanguage
  IShow.show IShow:SupportedLanguage LambdaCalculusTypesᵗ = "LambdaCalculusTypes"
  IShow.show IShow:SupportedLanguage Testᵗ = "Test"

getSupportedLanguages : List SupportedLanguage
getSupportedLanguages = Testᵗ ∷ []


record ∑𝔏ω {n : ℕ} {F : 𝔏 ^ n -> 𝔏} (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (F 𝑖)) : 𝒰ω where
  constructor _,_
  field fst : 𝔏 ^ n
  field snd : A fst

open ∑𝔏ω public


open import Verification.Experimental.Data.Expr.Variant.Base.InferenceTask
open import Verification.Experimental.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary

getInferenceTask : SupportedLanguage -> ∑𝔏ω InferenceTask
getInferenceTask LambdaCalculusTypesᵗ = {!!}
getInferenceTask Testᵗ = _ , BaseExprInferenceTask 𝕋ΛTypeData



