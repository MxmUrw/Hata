
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

open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteCoproductCategory

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Factorization

module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  private
    𝖩 : 𝒰 _
    𝖩 = Jdg₂ ⟨ K ⟩

  Splitter = Free-𝐌𝐨𝐧 (List 𝖩)

  mutual
    getSplitter-inter : {Γ : List 𝖩} {Δ : Free-𝐌𝐨𝐧 𝖩} {𝔍 : Free-𝐌𝐨𝐧 𝖩} -> (Σ : List 𝖩) -> Pat-inter Γ Δ 𝔍 -> Splitter
    getSplitter-inter Σ (incl {𝔍} {j ⇒ α} x) = getSplitter (Σ ⋆ j) x
    getSplitter-inter Σ (tsx ⋆-⧜ tsy) = getSplitter-inter Σ tsx ⋆ getSplitter-inter Σ tsy
    getSplitter-inter Σ ◌-⧜ = ◌

    getSplitter : ∀{𝔍} {a : 𝖩} -> (List 𝖩) -> 𝔍 ⊩-inter a -> Splitter
    getSplitter Σ (app-meta Γ α) = incl Σ
    getSplitter Σ (app-var x ts) = getSplitter-inter Σ ts
    getSplitter Σ (app-con x ts) = getSplitter-inter Σ ts





