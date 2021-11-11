
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
print-ℒHM A Γ (slet name t s) = node sletᵗ ( incl (print-ℒHM _ _ t)
                                            ∷ bind name (incl (print-ℒHM _ _ s))
                                            ∷ [])
print-ℒHM A Γ (app x y) = node appᵗ (incl (print-ℒHM A Γ x) ∷ incl (print-ℒHM A Γ y) ∷ [])
print-ℒHM A Γ (lam name t) = node lamᵗ (bind name (incl (print-ℒHM _ _ t)) ∷ [])

mutual
  print⁻¹-ℒHM' : ∀ {A Γ} -> SyntaxTreeBinding 𝒹-ℒHM A Γ 0 -> UntypedℒHMᵈ A Γ
  print⁻¹-ℒHM' (hole x) = hole x
  print⁻¹-ℒHM' (incl x) = print⁻¹-ℒHM _ x

  print⁻¹-ℒHM : ∀ {A} -> SyntaxTree 𝒹-ℒHM A ⟶ UntypedℒHM A
  print⁻¹-ℒHM Γ (hole x) = hole x
  print⁻¹-ℒHM Γ (var i x) = var x
  print⁻¹-ℒHM Γ (node lamᵗ (hole x ∷ [])) = hole x
  print⁻¹-ℒHM Γ (node lamᵗ (bind name x ∷ [])) = lam name (print⁻¹-ℒHM' x)
  print⁻¹-ℒHM Γ (node appᵗ (x ∷ (y ∷ []))) = app (print⁻¹-ℒHM' x) (print⁻¹-ℒHM' y)
  print⁻¹-ℒHM Γ (node sletᵗ (x ∷ (hole y ∷ []))) = {!slet (print⁻¹-ℒHM' x) (hole y)!}
  print⁻¹-ℒHM Γ (node sletᵗ (x ∷ (bind name y ∷ []))) = {!!}
  print⁻¹-ℒHM Γ (annotation x x₁) = {!!}

-- {!app (print⁻¹-ℒHM _ x) (print⁻¹-ℒHM _ y)!}

