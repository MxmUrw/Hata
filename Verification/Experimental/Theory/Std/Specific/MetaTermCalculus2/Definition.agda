
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Definition where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ2
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple

_<$>_ = map

Rule = Rule-⦿
-- Jdg = Jdg-⦿


-- pattern ⦋⦌ = []
-- pattern ⦋_⦌ a = [] ,, a
-- pattern ⦋_،_⦌ a b = [] ,, a ,, b
-- pattern ⦋_،_،_⦌ a b c = [] ,, a ,, b ,, c


-- | We define the *MetaTermCalculus*, which is a presentation of a
--   higher order rewriting system with meta variables.
--   The behaviour of these meta variables currently is slightly biased
--   towards the usual non-dependent or dependent type theories;
--   more exotic ones would need a slight modification. But since I do not
--   have good examples at the moment, it is difficult to predict how
--   the generalization should look like. Even though, it should not be
--   expensive to do so, once more information is available.

-- | In this approach we try out the fully monoidal version,
--   where no diagonal in the CwJ is required. Furthermore, the types
--   of the MTC have a rule;context shape, to be near the CwJ formulation.


record MetaTermCalculus (K : Kinding 𝑗) (𝑖 : 𝔏): 𝒰 (𝑗 ⁺ ､ 𝑖 ⁺) where
  field TermCon : (τ : List (Jdg ⟨ K ⟩)) -> Jdg ⟨ K ⟩ -> 𝒰 (𝑖 ⊔ 𝑗)

open MetaTermCalculus public


macro
  MTC : (K : Kinding 𝑗) -> ∀ 𝑖 -> SomeStructure
  MTC K 𝑖 = #structureOn (MetaTermCalculus K 𝑖)

module _ {K : Kinding 𝑗} (A B : MTC K 𝑖) where
  -- record isHom-MTC (f : MetaKind A -> MetaKind B) : 𝒰 𝑖 where
  --   -- field map-varzero : f (varzero A) ≡ varzero B
  --   -- field map-varsuc : f (varsuc A) ≡ varsuc B
  --   field map-TermCon : ∀ ρ -> TermCon A ρ -> TermCon B (map f ρ)
  -- Hom-MTC = _ :& isHom-MTC

  postulate
    Hom-MTC : 𝒰 (𝑗 ⊔ 𝑖)

module _ {K : Kinding 𝑗} where
  instance
    isCategory:MTC : isCategory (MetaTermCalculus K 𝑖)
    isCategory.Hom isCategory:MTC = Hom-MTC
    isCategory.isSetoid:Hom isCategory:MTC = isSetoid:byPath
    isCategory.id isCategory:MTC = {!!}
    isCategory._◆_ isCategory:MTC = {!!}
    isCategory.unit-l-◆ isCategory:MTC = {!!}
    isCategory.unit-r-◆ isCategory:MTC = {!!}
    isCategory.unit-2-◆ isCategory:MTC = {!!}
    isCategory.assoc-l-◆ isCategory:MTC = {!!}
    isCategory.assoc-r-◆ isCategory:MTC = {!!}
    isCategory._◈_ isCategory:MTC = {!!}


record Jdg₂ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _∣_⇒_
  field fst : List A
  field snd : List (Jdg A)
  field thd : Jdg A
infix 4 _∣_⇒_

module MTCDefinitions {K : Kinding 𝑗} (γ : MetaTermCalculus K 𝑖) where

  mutual
    data _⊩ᶠ-var_ : (𝔍s : List (Jdg ⟨ K ⟩)) -> Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖) where
      -- suc  : ∀{𝔍 Γ Δ α β} -> 𝔍 ⊩ᶠ (Γ ∣ [] ⇒ ∂ₖ α) -> 𝔍 ⊩ᶠ-var (Γ ∣ Δ ⇒ β) ->  𝔍 ⊩ᶠ-var ((α ∷ Γ) ∣ Δ ⇒ β)
      -- zero : ∀{𝔍 Γ α}      -> 𝔍 ⊩ᶠ (Γ ∣ [] ⇒ ∂ₖ α) -> 𝔍 ⊩ᶠ-var ((α ∷ Γ) ∣ [] ⇒ α)


    data _⊩ᶠ_ : (𝔍s : List (Jdg ⟨ K ⟩)) -> Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖) where
      meta : ∀{αs α} -> ⦋ αs ⊢ α ⦌ ⊩ᶠ ([] ∣ [] ⇒ (αs ⊢ α))
      -- lam  : ∀{𝔍s Γ Δ α β} -> 𝔍s ⊩ᶠ (((α) ∷ Γ) ∣ Δ ⇒ β) -> 𝔍s ⊩ᶠ (Γ ∣ (([] ⊢ α) ∷ Δ) ⇒ β)
      lam  : ∀{𝔍 𝔍' Γ Δ α αs β} -> 𝔍 ⊩ᶠ (Γ ∣ [] ⇒ ([] ⊢ ∂ₖ α))
                                  -> 𝔍' ⊩ᶠ ((Γ ⋆ (α ∷ [])) ∣ Δ ⇒ (αs ⊢ β))
                                  -> (𝔍 ⋆ 𝔍') ⊩ᶠ (Γ ∣ Δ ⇒ ((α ∷ αs) ⊢ β))
      app  : ∀{𝔍s 𝔍s' 𝔎s Γ Δ 𝔧 β}
            -> (𝔍s ⋆ 𝔍s' ≣ 𝔎s)
            -> 𝔍s ⊩ᶠ (Γ ∣ (𝔧 ∷ Δ) ⇒ β) -> 𝔍s' ⊩ᶠ (Γ ∣ [] ⇒ 𝔧)
            -> 𝔎s ⊩ᶠ (Γ ∣ Δ ⇒ β)

      con : ∀{Γ Δ α} -> TermCon γ Δ α -> [] ⊩ᶠ (Γ ∣ Δ ⇒ α)

      -- var : ∀{𝔍 Γ Δ α} -> 𝔍 ⊩ᶠ-var (Γ ∣ Δ ⇒ α) -> 𝔍 ⊩ᶠ (Γ ∣ Δ ⇒ α)

  _⊩ᶠ'_ : (𝔍s : List (Jdg ⟨ K ⟩)) -> Jdg ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖)
  _⊩ᶠ'_ 𝔍 (αs ⊢ α) = 𝔍 ⊩ᶠ ([] ∣ [] ⇒ (αs ⊢ α))


data Subs {K : 𝒰 𝑖} (R : List K -> K -> 𝒰 𝑗) : (Γ : List K) -> (Δ : List K) -> 𝒰 (𝑖 ､ 𝑗) where
  [] : Subs R [] []
  _∷_ : ∀{Γ Γ' Δ k} -> R Γ k -> Subs R Γ' Δ -> Subs R (Γ ⋆ Γ') (k ∷ Δ)

module _ {K : Kinding 𝑗} where
  record MTCCat (γ : MetaTermCalculus K 𝑖) : (𝒰 𝑗) where
    constructor incl
    field ⟨_⟩ : List (Jdg ⟨ K ⟩)

  open MTCCat public

  module _ {γ : MetaTermCalculus K 𝑖} where
    open MTCDefinitions γ
    instance
      isCategory:MTCCat : isCategory (MTCCat γ)
      isCategory.Hom isCategory:MTCCat = (λ 𝔍 𝔎 -> Subs (_⊩ᶠ'_) ⟨ 𝔍 ⟩ ⟨ 𝔎 ⟩)
      isCategory.isSetoid:Hom isCategory:MTCCat = isSetoid:byPath
      isCategory.id isCategory:MTCCat = {!!}
      isCategory._◆_ isCategory:MTCCat = {!!}
      isCategory.unit-l-◆ isCategory:MTCCat = {!!}
      isCategory.unit-r-◆ isCategory:MTCCat = {!!}
      isCategory.unit-2-◆ isCategory:MTCCat = {!!}
      isCategory.assoc-l-◆ isCategory:MTCCat = {!!}
      isCategory.assoc-r-◆ isCategory:MTCCat = {!!}
      isCategory._◈_ isCategory:MTCCat = {!!}

    instance
      isMonoidal:MTCCat : isMonoidal ′(MTCCat γ)′
      isMonoidal:MTCCat = {!!}

    isCwJ:MTCCat : isCwJ K ′(MTCCat γ)′
    isCwJ:MTCCat = {!!}

-- category
--       
--       {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}


    -- meta : ∀{𝔧} -> OptMeta 𝔧 (isHiddenMeta σ) (Μ ⊢-Ctx-⦿_) -> Μ ⊩ᶠ (𝔧 ◀ main)
    -- var : ∀{Γ τ} -> (Μ ⊩ᶠ (Γ ⊢ τ ◀ var)) -> Μ ⊩ᶠ (Γ ⊢ τ ◀ main)
    -- con :  ∀{Γ τ τ'} -> (⟦ τ ⟧-R ≣ τ') -> (TermCon σ τ) -> Μ ⊩ᶠ (Γ ⊢ τ' ◀ main)
    -- lam : ∀{Γ α β} -> Μ ⊩ᶠ ((Γ ,, α) ⊢ β ◀ main) -> Μ ⊩ᶠ (Γ ⊢ (α ⇒ β) ◀ main)
    -- app : ∀{Γ α β} -> Μ ⊩ᶠ (Γ ⊢ (α ⇒ β) ◀ main) -> Μ ⊩ᶠ (Γ ⊢ α ◀ main) -> Μ ⊩ᶠ (Γ ⊢ β ◀ main)

    -- suc  : ∀{Γ α β} -> Μ ⊩ᶠ (Γ ⊢ ∂ₘ σ α ◀ main)  -> Μ ⊩ᶠ (Γ ⊢ β ◀ var) -> Μ ⊩ᶠ ((Γ ,, α) ⊢ β ◀ var)
    -- zero : ∀{Γ α}   -> Μ ⊩ᶠ (Γ ⊢ ∂ₘ σ α ◀ main) -> Μ ⊩ᶠ ((Γ ,, α) ⊢ α ◀ var)



