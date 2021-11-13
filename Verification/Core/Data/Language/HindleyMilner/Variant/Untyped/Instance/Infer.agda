
module Verification.Core.Data.Language.HindleyMilner.Variant.Untyped.Instance.Infer where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Set.AllOf.Setoid
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Data.AllOf.Tree
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Variant.Untyped.Definition


data ℒHMTokenType : 𝒰₀ where
  lamᵗ appᵗ sletᵗ : ℒHMTokenType


tokenSize-ℒHM : ℒHMTokenType -> List (♮ℕ)
tokenSize-ℒHM lamᵗ = 1 ∷ []
tokenSize-ℒHM appᵗ = 0 ∷ 0 ∷ []
tokenSize-ℒHM sletᵗ = 0 ∷ 1 ∷ []

tokenName-ℒHM : ℒHMTokenType -> Text
tokenName-ℒHM lamᵗ = "λ"
tokenName-ℒHM appᵗ = "app"
tokenName-ℒHM sletᵗ = "let"

tokenList-ℒHM : List ℒHMTokenType
tokenList-ℒHM = lamᵗ ∷ appᵗ ∷ sletᵗ ∷ []

𝒹-ℒHM : SyntaxTreeData
𝒹-ℒHM = record
  { TokenType = ℒHMTokenType
  ; tokenSize = tokenSize-ℒHM
  ; tokenName = tokenName-ℒHM
  ; tokenList = tokenList-ℒHM
  }



print-ℒHM : ∀ A -> UntypedℒHM A ⟶ SyntaxTree 𝒹-ℒHM A
print-ℒHM A Γ (var {name} x) = var name x
print-ℒHM A Γ (hole x) = hole x
print-ℒHM A Γ (slet name t s) = node sletᵗ ( incl (incl (print-ℒHM _ _ t))
                                            ∷ incl (bind name (incl (print-ℒHM _ _ s)))
                                            ∷ [])
-- print-ℒHM A Γ (sletₓ t s) = node sletᵗ ( incl (incl (print-ℒHM _ _ t))
--                                         ∷ skipBinding (print-ℒHM _ _ s)
--                                         ∷ [])
print-ℒHM A Γ (app x y) = node appᵗ (incl (incl (print-ℒHM A Γ x)) ∷ incl (incl (print-ℒHM A Γ y)) ∷ [])
print-ℒHM A Γ (lam name t) = node lamᵗ (incl (bind name (incl (print-ℒHM _ _ t))) ∷ [])
-- print-ℒHM A Γ (lamₓ t) = node lamᵗ (skipBinding (print-ℒHM _ _ t) ∷ [])

mutual
  parse-ℒHM' : ∀ {A Γ} -> SyntaxTreeBinding 𝒹-ℒHM A Γ 0 -> UntypedℒHMᵈ A Γ
  parse-ℒHM' = {!!}
  -- parse-ℒHM' (hole x) = hole x
  -- parse-ℒHM' (incl x) = parse-ℒHM _ x

  parse-ℒHM : ∀ {A} -> SyntaxTree 𝒹-ℒHM A ⟶ UntypedℒHM (SyntaxTree 𝒹-ℒHM A)
  parse-ℒHM Γ (hole x) = hole (hole x)
  parse-ℒHM Γ (var i x) = var x
  parse-ℒHM Γ (node lamᵗ (skipBinding x ∷ [])) = hole (node lamᵗ (skipBinding x ∷ [])) -- lamₓ (parse-ℒHM _ x)
  parse-ℒHM Γ (node lamᵗ (incl (bind name (incl x)) ∷ [])) = lam name (parse-ℒHM _ x)
  parse-ℒHM Γ (node appᵗ (x ∷ (y ∷ []))) = {!!} -- app (parse-ℒHM' x) (parse-ℒHM' y)
  parse-ℒHM Γ (node sletᵗ (skipBinding x ∷ (skipBinding y ∷ []))) = hole ((node sletᵗ (skipBinding x ∷ (skipBinding y ∷ []))))
  parse-ℒHM Γ (node sletᵗ (skipBinding x ∷ (incl y ∷ []))) = hole ((node sletᵗ (skipBinding x ∷ (incl y ∷ []))))
  parse-ℒHM Γ (node sletᵗ (incl x ∷ (skipBinding y ∷ []))) = hole (node sletᵗ (incl x ∷ (skipBinding y ∷ [])))
  -- {!sletₓ (parse-ℒHM' x) (parse-ℒHM' y)!}
  parse-ℒHM Γ (node sletᵗ (incl (incl x) ∷ (incl (bind name (incl y)) ∷ []))) = slet name (parse-ℒHM _ x) (parse-ℒHM _ y)
  parse-ℒHM Γ (annotation x x₁) = {!!}

-- {!app (parse-ℒHM _ x) (parse-ℒHM _ y)!}

