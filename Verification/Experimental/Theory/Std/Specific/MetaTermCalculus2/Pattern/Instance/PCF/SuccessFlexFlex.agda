
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.SuccessFlexFlex where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Set.Function.Injective

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.FiniteIndexed.Property.Adjunction
open import Verification.Experimental.Data.NormalFiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal

open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Functor.RelativeAdjoint

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition


-- here i need to show that when i have (meta Mx tsx) (meta My tsy) then


module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where


  reset-with-meta : ∀{𝔍 : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {Γ Δ : ⟨ InjVars ⟩} {α : ⟨ K ⟩}
                  -- -> (M : 𝔍 ∍ ((⟨ ⟨ Δ ⟩ ⟩ ⇒ α))) ->
                  -> (s : Δ ⟶ Γ)
                  -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Γ ⟩ ⟩ ⇒ α) -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Δ ⟩ ⟩ ⇒ α)
  reset-with-meta {𝔍} {Γ} {Δ} σ (app-meta M s) = app-meta M ?
  reset-with-meta {𝔍} {Γ} {Δ} σ (app-var x x₁) = {!!}
  reset-with-meta {𝔍} {Γ} {Δ} σ (app-con x x₁) = {!!}

  unify-meta-meta-same : ∀{𝔍 : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {Γ Δ : ⟨ InjVars ⟩} {α : ⟨ K ⟩}
                  -> (M : 𝔍 ∍ ((⟨ ⟨ Δ ⟩ ⟩ ⇒ α))) -> (s t : Δ ⟶ Γ) -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Γ ⟩ ⟩ ⇒ α)
  unify-meta-meta-same M s t = app-meta M {!!}






