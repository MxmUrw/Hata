
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition as Curry
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition using (_∶_⊢_)
open import Verification.Experimental.Theory.Std.TypeTheory.Definition
open import Verification.Experimental.Computation.Question.Definition

private
  instance
    λCurry : isTypeTheory _ ′ Curry.Statement ′
    isTypeTheory.Termᵘ λCurry = Curry.Term-λ
    isTypeTheory.isSetoid:Term λCurry = it
    isTypeTheory._∶_ λCurry = λ t (_ , Γ ⊢ τ) -> t ∶ Γ ⊢ τ
    isTypeTheory.preserveType λCurry (incl refl-StrId) t = t


macro
  𝟙 : ∀{𝑖} -> SomeStructure
  𝟙 {𝑖} = #structureOn (⊤-𝒰 {𝑖})

private
  f : ⊤-𝒰 ⟶ TypeTheory _
  f = incl (const ′ Curry.Statement ′)

  g : ⊤-𝒰 ⟶ 𝐐𝐮𝐞𝐬𝐭 _
  g = f







