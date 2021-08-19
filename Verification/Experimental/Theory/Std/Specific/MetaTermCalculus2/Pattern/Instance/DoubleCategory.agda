
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.DoubleCategory where

open import Verification.Experimental.Conventions hiding (Structure ; _⊔_)
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

open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.FiniteCoproductCategory



module _ {A : 𝒰 𝑖} where
  FinFam : (as : Free-𝐌𝐨𝐧 A) -> (B : 𝒰 𝑗) -> 𝒰 _
  FinFam as B = ∀{a} -> (as ∍ a) -> B

  module _ {X : 𝒰 _} {{_ : Monoid 𝑗 on X}} where
    ⭑ : {as : Free-𝐌𝐨𝐧 A} (F : FinFam as X) -> X
    ⭑ {incl x} F = F incl
    ⭑ {as ⋆-⧜ bs} F = ⭑ {as} (λ x → F (left-∍ x)) ⋆ ⭑ {bs} (λ x → F (right-∍ x))
    ⭑ {◌-⧜} F = ◌


module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where


  private
    𝖩 : 𝒰 _
    𝖩 = Jdg₂ ⟨ K ⟩


  ν₋ : 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 ⟨ K ⟩ 𝖩 -> Free-𝐌𝐨𝐧 𝖩
  ν₋ (incl (incl a) , as)            = incl $ ⟨ ⟨ ⟨ ix as (a , incl) ⟩ ⟩ ⟩ ⇒ a
  ν₋ (incl (a ⋆-Free-𝐌𝐨𝐧 b) , as)   = ν₋ ((incl a) , {!!}) ⋆ ν₋ ((incl b) , {!!})
  ν₋ (incl ◌-Free-𝐌𝐨𝐧 , as)          = {!!}

  -- ν₋ (interren (incl (incl α)) αs) = incl (⟨ ⟨ αs incl ⟩ ⟩ ⇒ α)
  -- ν₋ (interren (incl (a ⋆-Free-𝐌𝐨𝐧 b)) αs) = 
  -- ν₋ (interren (incl ◌-Free-𝐌𝐨𝐧) αs) = {!!}

  ν₊ : Free-𝐌𝐨𝐧 𝖩 -> 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 ⟨ K ⟩ 𝖩
  ν₊ (incl (αs ⇒ α)) = incl (incl α) , indexed (λ x → incl (incl (incl αs)))
  -- interren (incl (incl α)) λ x → incl (incl αs)
  ν₊ (a ⋆-⧜ b) = {!!} -- ν₊ a ⋆ ν₊ b
  ν₊ ◌-⧜ = {!!}

  -- map-ν₊-∍ : ∀{a b : Free-𝐌𝐨𝐧 𝖩} -> (f : ν₊ b ⟶ ν₊ a) -> ∀{x} -> a ∍ x -> b ∍ x
  -- map-ν₊-∍ = {!!}

  ν₊-∍ : ∀{J : Free-𝐌𝐨𝐧 𝖩} -> ∀{a} -> (p : ⟨ base (ν₊ J) ⟩ ∍ a) -> J ∍ (⟨ ⟨ ⟨ ix (fib (ν₊ J)) (a , p) ⟩ ⟩ ⟩ ⇒ a)
  ν₊-∍ = {!!}


  -- 𝔍Fam : (Δ : Free-𝐌𝐨𝐧 𝖩) -> 𝒰 _
  -- 𝔍Fam Δ = ∀{i} -> Δ ∍ i -> Free-𝐌𝐨𝐧 𝖩

  -- merge𝔍Fam : ∀{Δ : Free-𝐌𝐨𝐧 𝖩} -> (𝔍s : 𝔍Fam Δ) -> Free-𝐌𝐨𝐧 𝖩
  -- merge𝔍Fam F = {!!}


  mutual
    data Pat-inter (Γ : List 𝖩) (Δ : Free-𝐌𝐨𝐧 𝖩) : (𝔍 : Free-𝐌𝐨𝐧 𝖩) -> 𝒰 𝑖 where
      lam : ∀{𝔍s : FinFam Δ (Free-𝐌𝐨𝐧 𝖩)} -> (∀{j} -> (p : Δ ∍ j) -> 𝔍s p ⊩-inter (γₗ Γ j)) -> Pat-inter Γ Δ (⭑ 𝔍s)

    data _⊩-inter_ : (𝔍s : Free-𝐌𝐨𝐧 𝖩) -> 𝖩 -> 𝒰 𝑖 where

      app-meta  : (Γ : ⟨ InjVars ⟩) (α : ⟨ K ⟩)
                -- -> (M : 𝔍 ∍ ((⟨ ⟨ Δ ⟩ ⟩ ⇒ α))) -- -> (s : (Δ) ⟶ (Γ))
                -> incl (⟨ ⟨ Γ ⟩ ⟩ ⇒ α) ⊩-inter (⟨ ⟨ Γ ⟩ ⟩  ⇒ α)

      app-var : ∀{𝔍 Γ Δ α}
              -> ι Γ ∍ (Δ ⇒ α) -> Pat-inter Γ (ι Δ) 𝔍
              -> 𝔍 ⊩-inter (Γ ⇒ α)

      app-con : ∀{𝔍 Γ Δ α}
              -> TermCon (Δ ⇒ α) -> Pat-inter Γ (ι Δ) 𝔍
              -> 𝔍 ⊩-inter (Γ ⇒ α)
  mutual
    {-# TERMINATING #-}
    compose-lam : {Γ : List 𝖩} {Δ : Free-𝐌𝐨𝐧 𝖩} -> {I J : Free-𝐌𝐨𝐧 𝖩}
                -> ν₊ I ⟶ ν₊ J -> Pat-inter Γ Δ I
                -> 𝑒𝑙 Δ ⟶ indexed (λ {j -> J ⊩ᶠ-pat (γₗ Γ j)})
                -- Pat-pats J Γ Δ
    compose-lam {Γ = Γ} {incl x₁} f (lam x) = λ {i incl → compose f (x incl)}
    compose-lam {Γ = Γ} {D ⋆-Free-𝐌𝐨𝐧 E} f (lam x) i (right-∍ p) = compose-lam {Δ = E} {!!} (lam (λ q → x (right-∍ q))) i (p)
    compose-lam {Γ = Γ} {D ⋆-Free-𝐌𝐨𝐧 E} f (lam x) i (left-∍ p) = {!!}
    -- lam (λ { i (left-∍ p) → {!!}
                                                               -- ; i (right-∍ p) -> {!!}
                                                               --  })
    compose-lam {Γ = Γ} {◌-Free-𝐌𝐨𝐧} f (lam x) = {!!}


    compose : ∀{I J : Free-𝐌𝐨𝐧 𝖩} {i : 𝖩} -> (ν₊ I ⟶ ν₊ J) -> I ⊩-inter i -> J ⊩ᶠ-pat i
    -- compose = {!!}
    compose {I} {J} f (app-meta Γ α) =
      let -- x = bas f
          y = ⟨ base f ⟩ α incl
          -- z = ix (fib (ν₊ J)) (α , y)
          -- v = ⟨ ⟨ z ⟩ ⟩
          w = fib f (α , incl)
      in app-meta (ν₊-∍ y) ⟨ w ⟩
    compose f (app-var x tsx) = app-var x (lam (compose-lam f tsx))
    compose f (app-con x tsx) = {!!}


{-
  compose f (app-meta Γ α) = app-meta {!!} {!!}
  compose f (app-var vx tsx) = app-var vx {!!}
  compose f (app-con x x₁) = {!!}



-}


{-
  -- record Interren : 𝒰 𝑖 where
  --   constructor interren
  --   field main : 𝐅𝐢𝐧𝐈𝐱 ⟨ K ⟩
  --   field interctx : ∀{i} -> ⟨ main ⟩ ∍ i -> ♮𝐑𝐞𝐧 𝖩

  -- open Interren public

  -- record Hom-Interren (I J : Interren) : 𝒰 𝑖 where
  --   field main-hom : main I ⟶ main J
  --   field interctx-hom : ∀{i} -> (p : ⟨ main I ⟩ ∍ i) -> interctx J (⟨ main-hom ⟩ _ p) ⟶ interctx I p

  -- open Hom-Interren public
-}
