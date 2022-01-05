
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Show where

open import Verification.Conventions

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

module _ {a : 𝒯FOSignature 𝑖} {{_ : ∀{xs} {x} -> IShow (Con a xs x)}} where
  private
    mutual
      lem-1s : ∀{Γ Δ} -> (𝒯⊔Terms a Γ Δ) -> Text
      lem-1s ◌-⧜ = "◌"
      lem-1s (incl x) = lem-1 x
      lem-1s (ts ⋆-⧜ ts₁) = lem-1s ts <> ", " <> lem-1s ts₁

      lem-1 : ∀{Γ : ⋆List (Sort a)} {τ : Sort a} -> (𝒯⊔Term a Γ τ) -> Text
      lem-1 (var x) = "var"
      lem-1 (con c x) = show c <> "(" <> lem-1s x <> ")"

  instance
    Show:𝒯⊔Term : ∀{Γ : ⋆List (Sort a)} {τ : Sort a} -> IShow (𝒯⊔Term a Γ τ)
    Show:𝒯⊔Term = record { show = lem-1 }
