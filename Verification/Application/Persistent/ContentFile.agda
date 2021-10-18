
module Verification.Application.Persistent.ContentFile where

open import Verification.Conventions
open import Verification.Experimental.Set.Discrete
open import Verification.Application.Configuration.Static
open import Verification.Experimental.Data.Expr.Variant.Base.Definition

open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.AllOf.List

open import Verification.Application.Persistent.Error
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation

record BaseContentFile : 𝒰₀ where
  constructor baseContentFile
  field language : String
  field content : BaseExpr


record ContentFile : 𝒰₀ where
  constructor contentFile
  field language : SupportedLanguage
  field content : BaseExpr

postulate
  parseContentFile : String -> PersistencyError + BaseContentFile


module _ {A : 𝒰 𝑖} {{_ : IShow A}} where
  isInList : String -> List A -> ⊤-𝒰 {ℓ₀} + A
  isInList a [] = left tt
  isInList a (x ∷ xs) with a ≟ show x
  ... | false = isInList a xs
  ... | true = right x


unbaseContentFile : BaseContentFile -> PersistencyError + ContentFile
unbaseContentFile (baseContentFile language content) = do

  -- parse the language of the file
  let languages = getSupportedLanguages
  let f = λ _ -> unsupportedLanguageError $ "The language '" <> language <>"' is not supported.\nSupported languages : " <> show languages
  language' <- mapLeft f (isInList language languages)

  return (contentFile language' content)







