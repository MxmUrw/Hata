
module Verification.Experimental.Theory.Computation.Problem.Specific.Parsing where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Theory.Formal.Presentation.Signature.SingleSorted.Definition

-- data Term-λ : 𝒰₀ where
--   app : (f g : Term-λ) -> Term-λ
--   lam : (t : Term-λ) -> Term-λ
--   var : ℕ -> Term-λ
--   par : Term-λ -> Term-λ

data TeSig : ℕ -> 𝒰₀ where
  `var` : String -> TeSig 0
  `lam` : String -> TeSig 1
  `app` : TeSig 2
  `par` : TeSig 1

Term-λ = Term {ℓ₀} TeSig

-- data Tok-λ : 


-- data TokKind : 𝒰₀ where
--   varK symK : TokKind

-- Tokens : 𝒰₀
-- Tokens = List (String ×-𝒰 TokKind)

-- π-Term : Term-λ -> Tokens
-- π-Term = {!!}



