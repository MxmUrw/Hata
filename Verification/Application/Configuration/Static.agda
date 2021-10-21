
module Verification.Application.Configuration.Static where

open import Verification.Conventions

open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.Task


data SupportedLanguage : 𝒰₀ where
  LambdaCalculusTypesᵗ : SupportedLanguage

instance
  IShow:SupportedLanguage : IShow SupportedLanguage
  IShow.show IShow:SupportedLanguage LambdaCalculusTypesᵗ = "LambdaCalculusTypes"

getSupportedLanguages : List SupportedLanguage
getSupportedLanguages = LambdaCalculusTypesᵗ ∷ []


record ∑𝔏ω {n : ℕ} {F : 𝔏 ^ n -> 𝔏} (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (F 𝑖)) : 𝒰ω where
  constructor _,_
  field fst : 𝔏 ^ n
  field snd : A fst

open ∑𝔏ω public

getInferenceTask : SupportedLanguage -> ∑𝔏ω InferenceTask
getInferenceTask = {!!}



