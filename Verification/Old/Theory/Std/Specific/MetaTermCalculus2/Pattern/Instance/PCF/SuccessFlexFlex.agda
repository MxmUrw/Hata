
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.SuccessFlexFlex where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Set.Function.Injective

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Adjunction
open import Verification.Core.Data.NormalFiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Renaming.Instance.hasEqualizers

open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Functor.RelativeAdjoint
open import Verification.Core.Category.Std.Limit.Specific.Equalizer.Definition

open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition


-- here i need to show that when i have (meta Mx tsx) (meta My tsy) then


module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where


  reset-with-meta : ∀{𝔍 : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {Γ Δ : ⟨ InjVars ⟩} {α : ⟨ K ⟩}
                  -- -> (M : 𝔍 ∍ ((⟨ ⟨ Δ ⟩ ⟩ ⇒ α))) ->
                  -> (s : Δ ⟶ Γ)
                  -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Γ ⟩ ⟩ ⇒ α) -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Δ ⟩ ⟩ ⇒ α)
  reset-with-meta {𝔍} {Γ} {Δ} σ (app-meta M s) = app-meta M {!!}
  reset-with-meta {𝔍} {Γ} {Δ} σ (app-var x x₁) = {!!}
  reset-with-meta {𝔍} {Γ} {Δ} σ (app-con x x₁) = {!!}

  unify-meta-meta-same : ∀{𝔍 : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {Γ Δ : ⟨ InjVars ⟩} {α : ⟨ K ⟩}
                  -> (M : 𝔍 ∍ ((⟨ ⟨ Γ ⟩ ⟩ ⇒ α))) -> (s t : Γ ⟶ Δ) -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Δ ⟩ ⟩ ⇒ α)
  unify-meta-meta-same M s t = app-meta {Δ = Eq {{hasEqualizers:♮𝐑𝐞𝐧}} s t} {!!} {!!}






