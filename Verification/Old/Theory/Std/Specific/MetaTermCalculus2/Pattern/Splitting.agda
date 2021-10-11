
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Splitting where

open import Verification.Experimental.Conventions hiding (Structure ; _⊔_ ; extend)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Order.Lattice hiding (⊥)
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Opposite.Instance.Monoid
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.MultiRenaming.Definition
open import Verification.Experimental.Data.MultiRenaming.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.MultiRenaming.Shift

open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteCoproductCategory

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Factorization

module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  -- private
  --   (Jdg₂ ⟨ K ⟩) : 𝒰 _
  --   (Jdg₂ ⟨ K ⟩) = Jdg₂ ⟨ K ⟩

  Splitter = Free-𝐌𝐨𝐧 (List (Jdg₂ ⟨ K ⟩))

  mutual
    getSplitter-inter : {Γ : List (Jdg₂ ⟨ K ⟩)} {Δ : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {𝔍 : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} -> (Σ : List (Jdg₂ ⟨ K ⟩)) -> Pat-inter Γ Δ 𝔍 -> Splitter
    getSplitter-inter Σ (incl {𝔍} {j ⇒ α} x) = getSplitter-impl (Σ ⋆ j) x
    getSplitter-inter Σ (tsx ⋆-⧜ tsy) = getSplitter-inter Σ tsx ⋆ getSplitter-inter Σ tsy
    getSplitter-inter Σ ◌-⧜ = ◌

    getSplitter-impl : ∀{𝔍} {a : (Jdg₂ ⟨ K ⟩)} -> (List (Jdg₂ ⟨ K ⟩)) -> 𝔍 ⊩-inter a -> Splitter
    getSplitter-impl Σ (app-meta Γ α) = incl Σ
    getSplitter-impl Σ (app-var x ts) = getSplitter-inter Σ ts
    getSplitter-impl Σ (app-con x ts) = getSplitter-inter Σ ts

    getSplitter : ∀{𝔍} {a : (Jdg₂ ⟨ K ⟩)} -> 𝔍 ⊩-inter a -> Splitter
    getSplitter = getSplitter-impl []

  getObj : ∀{J : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {i : (Jdg₂ ⟨ K ⟩)} -> (t : J ⊩ᶠ-pat i) -> Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)
  getObj {J} {i} t = ν₋ (⟨ 分 splitter ⟩ start)
    where
      splitter = getSplitter (decompose t .snd .snd)

      start : 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 ⟨ K ⟩ (Jdg₂ ⟨ K ⟩)
      start = ν₊ (incl i)


  lem-10 : ∀{J : Free-𝐌𝐨𝐧 (Jdg₂ ⟨ K ⟩)} {i : (Jdg₂ ⟨ K ⟩)} -> (t : J ⊩ᶠ-pat i) -> decompose t .fst ≣ getObj t
  lem-10 (app-meta M s) = refl-≣
  lem-10 (app-var x x₁) = {!!}
  lem-10 (app-con x x₁) = {!!}



