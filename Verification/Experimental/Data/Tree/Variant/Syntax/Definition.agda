
module Verification.Experimental.Data.Tree.Variant.Syntax.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Nat.Definition
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition

open import Verification.Experimental.Data.Tree.Variant.Syntax.Data


module _ (𝒹 : SyntaxTreeData) where
  data SyntaxTreeᵈ (A : 人ℕ -> 𝒰₀) : (Γ : 人ℕ) -> 𝒰₀ where
    hole : ∀{Γ} -> A Γ -> SyntaxTreeᵈ A Γ
    var : ∀ {Γ i} -> Γ ∍ i -> SyntaxTreeᵈ A Γ
    node : ∀{Γ} -> (t : TokenType 𝒹) -> ((i : Fin-R (tokenSize 𝒹 t)) -> SyntaxTreeᵈ A (Γ ⋆ ι-人ℕ (tokenBind 𝒹 t i))) -> SyntaxTreeᵈ A Γ
    annotation : ∀{Γ} -> Text -> SyntaxTreeᵈ A Γ -> SyntaxTreeᵈ A Γ


  SyntaxTreeᵘ : 𝐈𝐱 人ℕ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 人ℕ (𝐔𝐧𝐢𝐯 ℓ₀)
  SyntaxTreeᵘ A = indexed (SyntaxTreeᵈ (ix A))

  macro SyntaxTree = #structureOn SyntaxTreeᵘ



