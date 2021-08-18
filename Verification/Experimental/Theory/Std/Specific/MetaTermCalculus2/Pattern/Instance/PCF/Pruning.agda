
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.Pruning where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category


module _ {𝑖 : 𝔏} {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  prune : ∀{𝔍} {Γ Δ : ⟨ InjVars ⟩} {α : ⟨ K ⟩} -> (j : Δ ⟶ Γ) -> (t : 𝔍 ⊩ᶠ-pat (⟨ ⟨ Γ ⟩ ⟩ ⇒ α)) -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Δ ⟩ ⟩ ⇒ α)
  prune j (app-meta M s) = app-meta M {!!}
  prune j (app-var x x₁) = {!!}
  prune j (app-con x x₁) = {!!}

  data hasDecidableLifting-⧜𝐏𝐚𝐭 : {a b : ⧜𝐏𝐚𝐭 K} (f : a ⟶ b) -> 𝒰 𝑖 where

    app-meta  : ∀{𝔍} {Γ Δ : ⟨ InjVars ⟩} {α : ⟨ K ⟩}
              -> (M : 𝔍 ∍ ((⟨ ⟨ Δ ⟩ ⟩ ⇒ α))) -> (s : Δ ⟶ Γ)
              -> hasDecidableLifting-⧜𝐏𝐚𝐭 (incl (app-meta M s))




