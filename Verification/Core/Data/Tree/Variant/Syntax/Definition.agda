
module Verification.Core.Data.Tree.Variant.Syntax.Definition where

open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.List
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Substitution.Variant.Normal.Definition

open import Verification.Core.Data.Tree.Variant.Syntax.Data


module _ (𝒹 : SyntaxTreeData) where

  mutual
    data SyntaxTreeBinding (A : ⋆List Text -> 𝒰₀) : (Γ : ⋆List Text) (n : ♮ℕ) -> 𝒰₀ where
      -- hole : ∀{Γ n} -> A Γ -> SyntaxTreeBinding A Γ n -> SyntaxTreeBinding A Γ (tt ∷ n)
      incl : ∀{Γ} -> SyntaxTreeᵈ A Γ -> SyntaxTreeBinding A Γ 0
      bind : ∀{Γ n} -> (name : Text) -> SyntaxTreeBinding A (Γ ⋆ incl name) n -> SyntaxTreeBinding A Γ (tt ∷ n)

    data SyntaxTreeBindingWithHole (A : ⋆List Text -> 𝒰₀) : (Γ : ⋆List Text) (n : ♮ℕ) -> 𝒰₀ where
      skipBinding : ∀{Γ n} -> SyntaxTreeᵈ A Γ -> SyntaxTreeBindingWithHole A Γ n
      incl : ∀{Γ n} -> SyntaxTreeBinding A Γ n -> SyntaxTreeBindingWithHole A Γ n

    data SyntaxTreeᵈ (A : ⋆List Text -> 𝒰₀) : (Γ : ⋆List Text) -> 𝒰₀ where
      hole : ∀{Γ} -> A Γ -> SyntaxTreeᵈ A Γ
      var : ∀ {Γ} -> ∀ i -> Γ ∍ i -> SyntaxTreeᵈ A Γ
      node : ∀{Γ} -> (t : TokenType 𝒹)
                  -> Listᴰ (SyntaxTreeBindingWithHole A Γ) (tokenSize 𝒹 t)
                  -> SyntaxTreeᵈ A Γ
      annotation : ∀{Γ} -> Text -> SyntaxTreeᵈ A Γ -> SyntaxTreeᵈ A Γ


  SyntaxTreeᵘ : 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀) -> 𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)
  SyntaxTreeᵘ A = indexed (SyntaxTreeᵈ (ix A))

  macro SyntaxTree = #structureOn SyntaxTreeᵘ



