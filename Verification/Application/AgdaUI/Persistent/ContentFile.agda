
module Verification.Application.AgdaUI.Persistent.ContentFile where

open import Verification.Conventions
open import Verification.Core.Set.Discrete
open import Verification.Application.AgdaUI.Configuration.Static
open import Verification.Core.Data.Expr.Variant.Base.Definition

open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List

open import Verification.Application.AgdaUI.Persistent.Error
open import Verification.Core.Category.Std.Functor.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.TypeMonadNotation

{-# FOREIGN GHC import Hata.Runtime.Application.Persistent.ContentFile #-}

record BaseContentFile : 𝒰₀ where
  constructor baseContentFile
  field language : Text
  field content : Text

{-# COMPILE GHC BaseContentFile = data BaseContentFile (BaseContentFile) #-}


record ContentFile : 𝒰₀ where
  constructor contentFile
  field language : SupportedLanguage
  field content : Text

postulate
  parseContentFile : String -> Text + BaseContentFile

{-# COMPILE GHC parseContentFile = parseContentFile #-}


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







