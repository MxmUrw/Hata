
module Verification.Core.Theory.Std.Specific.ProductTheory.Unification.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition



record ProductTheory (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  field Sort : 𝒰 𝑖
  field {{isDiscrete:Sort}} : isDiscrete Sort
  field {{isSet-Str:Sort}} : isSet-Str Sort
  field Con : List Sort -> Sort -> 𝒰 𝑖
  field {{isDiscrete:Con}} : ∀{αs α} -> isDiscrete (Con αs α)
open ProductTheory public

module _ (𝑖 : 𝔏) where
  macro 𝕋× = #structureOn (ProductTheory 𝑖)

  𝒜 = ProductTheory 𝑖

Type-𝕋× : ProductTheory 𝑖 -> 𝒰 𝑖
Type-𝕋× a = Sort a




data Term₁-𝕋× (a : 𝕋× 𝑖) : (Γ : ⋆List (Type-𝕋× a)) (τ : Type-𝕋× a) -> 𝒰 𝑖 where
  var : ∀{τ Γ} -> Γ ∍ τ -> Term₁-𝕋× a Γ τ
  con : ∀{Γ αs α} -> (c : Con a αs α) -> CtxHom (Term₁-𝕋× a) ((ι αs)) (Γ) -> Term₁-𝕋× a Γ α


Term-𝕋× : (a : 𝕋× 𝑖) -> (𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× a)) -> (𝐈𝐱 (Type-𝕋× a) (𝐔𝐧𝐢𝐯 𝑖))
Term-𝕋× a Γ = indexed (λ τ → Term₁-𝕋× a ⟨ Γ ⟩ τ)

Terms-𝕋× : (𝑨 : 𝕋× 𝑖) -> (Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) -> (Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) -> 𝒰 𝑖
Terms-𝕋× 𝑨 Γ Δ = CtxHom (Term₁-𝕋× 𝑨) ⟨ Γ ⟩ ⟨ Δ ⟩

分Term = Term₁-𝕋×

全Term = Terms-𝕋×


module _ {𝑨 : 𝕋× 𝑖} where
  mutual
    data VarPath-Terms-𝕋× : ∀{Γ Δ} -> (t : Terms-𝕋× 𝑨 Δ Γ) -> {s : Sort 𝑨} -> (⟨ Γ ⟩ ∍ s) -> 𝒰 𝑖 where
      left-Path : ∀{Γ Δ Δ'} -> {t : Terms-𝕋× 𝑨 Δ Γ} -> {t' : Terms-𝕋× 𝑨 Δ' Γ} -> {s : Sort 𝑨} -> {v : ⟨ Γ ⟩ ∍ s}
                  -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t ⋆-⧜ t') v

      right-Path : ∀{Γ Δ Δ'} -> {t : Terms-𝕋× 𝑨 Δ Γ} -> {t' : Terms-𝕋× 𝑨 Δ' Γ} -> {s : Sort 𝑨} -> {v : ⟨ Γ ⟩ ∍ s}
                  -> (p : VarPath-Terms-𝕋× t v) -> VarPath-Terms-𝕋× (t' ⋆-⧜ t) v

      incl : ∀{Γ τ} -> {t : Term₁-𝕋× 𝑨 Γ τ} -> {s : Sort 𝑨} -> {v : Γ ∍ s}
                  -> (p : VarPath-Term-𝕋× t v) -> VarPath-Terms-𝕋× (incl t) v

    data VarPath-Term-𝕋× : ∀{Γ τ} -> (t : Term₁-𝕋× 𝑨 Γ τ) -> {s : Sort 𝑨} -> (Γ ∍ s) -> 𝒰 𝑖 where
      var : ∀{Γ s} -> (x : Γ ∍ s) -> VarPath-Term-𝕋× (var x) x
      con : ∀{Γ αs α s} {x : Γ ∍ s} -> (c : Con 𝑨 αs α) -> {ts : Terms-𝕋× 𝑨 (incl (ι αs)) (incl Γ) }
            -> VarPath-Terms-𝕋× ts x
            -> VarPath-Term-𝕋× (con c ts) x



