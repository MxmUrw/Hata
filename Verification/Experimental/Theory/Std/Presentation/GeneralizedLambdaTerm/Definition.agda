
module Verification.Experimental.Theory.Std.Presentation.GeneralizedLambdaTerm.Definition where

open import Verification.Experimental.Conventions
open import Application.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Computation.Question.Definition
open import Verification.Experimental.Computation.Question.Specific.Small
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Sum.Instance.Monad
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Category.Std.Monad.Definition

{-# FOREIGN GHC import Hata.Runtime.Service.Parse.GeneralizedLambdaTerm #-}



-------------------------
-- unchecked generalized lambda term signature




data TermBase-GL : 𝒰₀ where
  te : String -> List TermBase-GL -> TermBase-GL
  var : String -> TermBase-GL
  lam : String -> TermBase-GL -> TermBase-GL
  app : TermBase-GL -> TermBase-GL -> TermBase-GL

-- {-# COMPILE GHC Signature-GL = data Signature_GL (Signature_GL)  #-}
{-# COMPILE GHC TermBase-GL = data TermBase_GL (Te | Var | Lam | App)  #-}


postulate
  parseTerm-GL : List String -> String -> Error +-𝒰 TermBase-GL

{-# COMPILE GHC parseTerm-GL = parseTerm_GL #-}

-------------------------
-- Terms where keywords are only from the signature
-- and have the right number of arguments

record Signature-GL : 𝒰₀ where
  field num : ℕ
  field keywords : Vec String num
  field arity : Vec ℕ num

open Signature-GL

data Term-GL (σ : Signature-GL) : 𝒰₀ where
  te : (keyword : String) -> ∀ i -> (lookup i (σ .keywords) ≣ keyword)
     -> Vec (Term-GL σ) (lookup i (σ .arity))
     -> Term-GL σ
  var : String -> Term-GL σ
  lam : String -> Term-GL σ -> Term-GL σ
  app : Term-GL σ -> Term-GL σ -> Term-GL σ

instance
  isQuestion:Signature-GL : isQuestion _ Signature-GL
  isQuestion:Signature-GL = answerWith (λ σ → String -> Error + Term-GL σ)


module _ {A : 𝒰 𝑖} where
  Vec→List : Vec A n -> List A
  Vec→List [] = []
  Vec→List (v ∷ vs) = v ∷ Vec→List vs

check-TermBase : ∀(σ) -> TermBase-GL -> Error + Term-GL σ
check-TermBase σ (te x x₁) = {!!}
check-TermBase σ (var x) = right (var x)
check-TermBase σ (lam x t) = do
  t <- check-TermBase σ t
  return (lam x t)
check-TermBase σ (app t s) = do
  t' <- check-TermBase σ t
  s' <- check-TermBase σ s
  return (app t' s')



private
  ρ : Signature-GL -> TRIVIAL {ℓ₀}
  ρ = const tt

instance
  isReduction:ρ : isReductive ′ Signature-GL ′ TRIVIAL ρ
  isReduction:ρ = reductive λ {σ} x input →
    let σ' = Vec→List (σ. keywords)
    in do
      t <- parseTerm-GL σ' input
      check-TermBase σ t

    --     baseTerm = 
    -- in case baseTerm of
    --      (left)
    --      (λ t -> check-TermBase σ t)



-------------------------
-- scope checked generalized lambda signature







