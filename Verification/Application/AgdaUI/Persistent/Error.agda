
module Verification.Application.AgdaUI.Persistent.Error where

open import Verification.Conventions

data PersistencyError : 𝒰₀ where
  parseError : String -> PersistencyError
  unsupportedLanguageError : String -> PersistencyError

instance
  IShow:PersistencyError : IShow PersistencyError
  IShow.show IShow:PersistencyError (parseError x) = "Error during parsing of file:\n " <> x
  IShow.show IShow:PersistencyError (unsupportedLanguageError x) = x

