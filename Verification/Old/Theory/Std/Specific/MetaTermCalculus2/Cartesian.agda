
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Cartesian where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

module _ {K : 𝒰 𝑖} (R : List K -> K -> 𝒰 𝑗) where
  data Subs : (Γ : (List K)) -> (Δ : List K) -> 𝒰 (𝑖 ､ 𝑗) where
    [] : ∀{Γ} -> Subs Γ []
    _∷_ : ∀{Γ Δ k} -> R Γ k -> Subs Γ Δ -> Subs Γ (k ∷ Δ)

module _ {K : 𝒰 𝑖} {R : List K -> K -> 𝒰 𝑗} where
  getvar : ∀{Γ Δ k} -> Subs R Γ Δ -> Δ ⊨-var k -> R Γ k
  getvar (x ∷ s) zero = x
  getvar (x ∷ s) (suc i) = getvar s i


record Jdg₂ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _∣_⇒_
  field fst : List A
  field snd : List (Jdg A)
  field thd : Jdg A
infix 4 _∣_⇒_

record MetaTermCalculus (K : Kinding 𝑗) (𝑖 : 𝔏): 𝒰 (𝑗 ⁺ ､ 𝑖 ⁺) where
  field TermCon : (τ : List (Jdg ⟨ K ⟩)) -> Jdg ⟨ K ⟩ -> 𝒰 (𝑖)

open MetaTermCalculus public

module MTCDefinitions {K : Kinding 𝑗} (γ : MetaTermCalculus K 𝑖) where


  data _⊩ᶠ↑_ : (𝔍s : List (Jdg₂ ⟨ K ⟩)) -> Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖) where
    meta : ∀{𝔍 Γ Δ α} -> 𝔍 ⊨-var (Γ ∣ Δ ⇒ α) -> 𝔍 ⊩ᶠ↑ (Γ ∣ Δ ⇒ α)
    lam  : ∀{𝔍 Γ Δ α αs β} -> (t : 𝔍 ⊩ᶠ↑ (Γ ∣ [] ⇒ ([] ⊢ ∂ₖ α)))
                            -> (s : 𝔍 ⊩ᶠ↑ ((α ∷ Γ) ∣ Δ ⇒ (αs ⊢ β)))
                            -> 𝔍 ⊩ᶠ↑ (Γ ∣ Δ ⇒ ((α ∷ αs) ⊢ β))
    app  : ∀{𝔍 Γ Δ 𝔧 β}
          -> (t : 𝔍 ⊩ᶠ↑ (Γ ∣ (𝔧 ∷ Δ) ⇒ β)) -> (s : 𝔍 ⊩ᶠ↑ (Γ ∣ [] ⇒ 𝔧))
          -> 𝔍 ⊩ᶠ↑ (Γ ∣ Δ ⇒ β)

    con : ∀{𝔍 Γ Δ α} -> TermCon γ Δ α -> 𝔍 ⊩ᶠ↑ (Γ ∣ Δ ⇒ α)

    var : ∀{𝔍 Γ α} -> Γ ⊨-var α -> 𝔍 ⊩ᶠ↑ (Γ ∣ [] ⇒ ([] ⊢ α))



