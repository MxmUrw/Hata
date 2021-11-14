
module Verification.Application.Configuration.Static where

open import Verification.Conventions

open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task


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


open import Verification.Core.Data.Expr.Variant.Token.Data
open import Verification.Core.Data.Expr.Variant.Token.Definition
open import Verification.Core.Data.Expr.Variant.AnnotatedList.Instance.Monad
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Monad
open import Verification.Core.Data.Expr.Variant.AnnotatedToken.Instance.Infer
-- open import Verification.Core.Theory.Std.Specific.ProductClosedTheory.Inference.Boundary
open import Verification.Core.Data.Tree.Variant.Syntax.Instance.Infer
open import Verification.Core.Data.Tree.Variant.Token.Instance.Infer
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.AllOf.Collection.Basics

open import Verification.Core.Algebra.AllOf.Pointed



--------------
-- test

data ℒHMTokenType : 𝒰₀ where
  lamᵗ appᵗ sletᵗ : ℒHMTokenType

tokenName-ℒHM : ℒHMTokenType -> Text
tokenName-ℒHM lamᵗ = "λ"
tokenName-ℒHM appᵗ = "app"
tokenName-ℒHM sletᵗ = "let"

tokenList-ℒHM : List ℒHMTokenType
tokenList-ℒHM = lamᵗ ∷ appᵗ ∷ sletᵗ ∷ []

my𝒹 : ATokenExprData
my𝒹 = record { TokenType = ℒHMTokenType ; tokenName = tokenName-ℒHM ; tokenList = tokenList-ℒHM }

--------------


getInferenceTask : SupportedLanguage -> ∑𝔏ω InferenceTask
getInferenceTask LambdaCalculusTypesᵗ = {!!}
getInferenceTask Testᵗ = _ , ATokenExprInferenceTask {𝒹 = my𝒹} {Ann = 0-𝐏𝐭𝐝} -- BaseExprInferenceTask {!!} -- {𝕋ΛTypeData} {𝕋ΛTypeData2} refl-≅



