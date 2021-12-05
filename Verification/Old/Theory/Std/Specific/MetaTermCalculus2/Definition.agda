
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Definition where

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

_<$>_ = map

Rule = Rule-⦿

join : ∀{K : 𝒰 𝑖} -> (List (List K)) -> List K
join ⦋⦌ = ⦋⦌
join (xs ∷ xss) = xs ⋆ join xss

module _ {K : 𝒰 𝑖} where
  -- sym-≣ : ∀{a b : K} -> (a ≣ b) -> b ≣ a
  -- sym-≣ refl-≣ = refl-≣

  trans-≣ : ∀{a b c : K} -> (a ≣ b) -> b ≣ c -> a ≣ c
  trans-≣ refl-≣ p = p

module _ {K : 𝒰 𝑖} where
  distr-join-⋆ : ∀{xs ys : List (List K)} -> join (xs ⋆ ys) ∼ join xs ⋆ join ys
  distr-join-⋆ {⦋⦌} {ys} = refl
  distr-join-⋆ {xs ∷ xss} {ys} = sym-≣ (trans-≣ (assoc-l-⋆ {a = xs} {b = join xss} {c = join ys}) (refl-StrId {x = xs} ≀⋆≀ sym-≣ (distr-join-⋆ {xs = xss})))


module _ {K : 𝒰 𝑖} (R : List K -> K -> 𝒰 𝑗) where
  data Subs : (Γ : List (List K)) -> (Δ : List K) -> 𝒰 (𝑖 ､ 𝑗) where
    [] : Subs [] []
    _∷_ : ∀{Γ Γ' Δ k} -> R Γ k -> Subs Γ' Δ -> Subs (Γ ∷ Γ') (k ∷ Δ)

  Hom-Subs : (Γ Δ : List K) -> 𝒰 _
  Hom-Subs Γ Δ = ∑ λ Γs -> (join Γs ≣ Γ) × Subs Γs Δ

module _ {K : 𝒰 𝑖} {R : List K -> K -> 𝒰 𝑗} where
  split-Subs : {Γ : List (List K)} -> {Δ Δ' : List K} -> Subs R Γ (Δ ⋆ Δ') -> ∑ λ Γ₀ -> ∑ λ Γ₁ -> (Γ ∼ Γ₀ ⋆ Γ₁) ×-𝒰 (Subs R Γ₀ Δ × Subs R Γ₁ Δ')
  split-Subs {Γ = ⦋⦌} {Δ = ⦋⦌} {.⦋⦌} [] = [] , [] , {!!} , [] , []
  split-Subs {Γ = Γ ∷ Γ₁} {Δ = ⦋⦌} {.(_ ∷ _)} (x ∷ s) = _ , _ , {!!} , [] , x ∷ s
  split-Subs {Γ = Γ ∷ Γs} {Δ = d ∷ D} {D'} (x ∷ s) =
    let Γ₂ , Γ₃ , p , s₂ , s₃ = split-Subs {Δ = D} {Δ' = D'} s
    in _ , _ , {!!} , (x ∷ s₂) , s₃

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
  field TermCon : (τ : List (Jdg ⟨ K ⟩)) -> Jdg ⟨ K ⟩ -> 𝒰 (𝑖)

open MetaTermCalculus public


macro
  MTC : (K : Kinding 𝑗) -> ∀ 𝑖 -> SomeStructure
  MTC K 𝑖 = #structureOn (MetaTermCalculus K 𝑖)

module _ {K : Kinding 𝑗} (A : MTC K 𝑖) (B : MTC K 𝑘) where
  -- record isHom-MTC (f : MetaKind A -> MetaKind B) : 𝒰 𝑖 where
  --   -- field map-varzero : f (varzero A) ≡ varzero B
  --   -- field map-varsuc : f (varsuc A) ≡ varsuc B
  --   field map-TermCon : ∀ ρ -> TermCon A ρ -> TermCon B (map f ρ)
  -- Hom-MTC = _ :& isHom-MTC
  record Hom-MTC : 𝒰 (𝑗 ⊔ 𝑖 ⊔ 𝑘) where
    field ⟨_⟩ : ∀ {Δ α} -> TermCon A Δ α -> TermCon B Δ α

  open Hom-MTC public

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

    -- data _⊩ᶠ-var_ : (𝔍s : List (Jdg ⟨ K ⟩)) -> Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖) where
    --   suc  : ∀{𝔍 Γ α β} -> 𝔍 ⊩ᶠ (Γ ∣ [] ⇒ ([] ⊢ ∂ₖ α)) -> 𝔍 ⊩ᶠ-var (Γ ∣ [] ⇒ β)
    --          ->  𝔍 ⊩ᶠ-var ((Γ ⋆ ⦋ α ⦌) ∣ [] ⇒ β)
    --   zero : ∀{𝔍 Γ α}      -> 𝔍 ⊩ᶠ (Γ ∣ [] ⇒ ([] ⊢ ∂ₖ α)) -> 𝔍 ⊩ᶠ-var ((Γ ⋆ ⦋ α ⦌) ∣ [] ⇒ ([] ⊢ α))


  data _⊩ᶠ_ : (𝔍s : List (Jdg ⟨ K ⟩)) -> Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖) where
    meta : ∀{αs α} -> ⦋ αs ⊢ α ⦌ ⊩ᶠ ([] ∣ [] ⇒ (αs ⊢ α))
    lam  : ∀{𝔍 𝔍' Γ Δ α αs β} -> 𝔍 ⊩ᶠ (Γ ∣ [] ⇒ ([] ⊢ ∂ₖ α))
                                -> 𝔍' ⊩ᶠ ((α ∷ Γ) ∣ Δ ⇒ (αs ⊢ β))
                                -> (𝔍 ⋆ 𝔍') ⊩ᶠ (Γ ∣ Δ ⇒ ((α ∷ αs) ⊢ β))
    app  : ∀{𝔍s 𝔍s' Γ Δ 𝔧 β}
          -- -> (𝔍s ⋆ 𝔍s' ≣ 𝔎s)
          -> 𝔍s ⊩ᶠ (Γ ∣ (𝔧 ∷ Δ) ⇒ β) -> 𝔍s' ⊩ᶠ (Γ ∣ [] ⇒ 𝔧)
          -- -> 𝔎s ⊩ᶠ (Γ ∣ Δ ⇒ β)
          -> (𝔍s' ⋆ 𝔍s) ⊩ᶠ (Γ ∣ Δ ⇒ β)

    con : ∀{Γ Δ α} -> TermCon γ Δ α -> [] ⊩ᶠ (Γ ∣ Δ ⇒ α)

    var : ∀{Γ α} -> Γ ⊨-var α -> [] ⊩ᶠ (Γ ∣ [] ⇒ ([] ⊢ α))

    -- var : ∀{𝔍 Γ Δ α} -> 𝔍 ⊩ᶠ-var (Γ ∣ Δ ⇒ α) -> 𝔍 ⊩ᶠ (Γ ∣ Δ ⇒ α)

  record MJdg (A : 𝒰 𝑘) : 𝒰 𝑘 where
    constructor _∣_⇒_
    field fst : List A
    field snd : List A
    field thd : Jdg A

  jdg₂ : ∀{A : 𝒰 𝑘} -> MJdg A -> Jdg₂ A
  jdg₂ (Γ ∣ Δ ⇒ α) = Γ ∣ (map ([] ⊢_) Δ) ⇒ (α)


  data _⊩ᶠ↑_ : (𝔍s : List (Jdg₂ ⟨ K ⟩)) -> Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖) where
    meta : ∀{Γ Δ α } -> ⦋ Γ ∣ Δ ⇒ α ⦌ ⊩ᶠ↑ (Γ ∣ Δ ⇒ α)
    lam  : ∀{𝔍 𝔍' Γ Δ α αs β} -> 𝔍 ⊩ᶠ↑ (Γ ∣ [] ⇒ ([] ⊢ ∂ₖ α))
                                -> 𝔍' ⊩ᶠ↑ ((α ∷ Γ) ∣ Δ ⇒ (αs ⊢ β))
                                -> (𝔍 ⋆ 𝔍') ⊩ᶠ↑ (Γ ∣ Δ ⇒ ((α ∷ αs) ⊢ β))
    app  : ∀{𝔍s 𝔍s' Γ Δ 𝔧 β}
          -> 𝔍s ⊩ᶠ↑ (Γ ∣ (𝔧 ∷ Δ) ⇒ β) -> 𝔍s' ⊩ᶠ↑ (Γ ∣ [] ⇒ 𝔧)
          -> (𝔍s ⋆ 𝔍s') ⊩ᶠ↑ (Γ ∣ Δ ⇒ β)

    con : ∀{Γ Δ α} -> TermCon γ Δ α -> [] ⊩ᶠ↑ (Γ ∣ Δ ⇒ α)

    var : ∀{Γ α} -> Γ ⊨-var α -> [] ⊩ᶠ↑ (Γ ∣ [] ⇒ ([] ⊢ α))

  -- ι₁-var : ∀{A : 𝒰 𝑘} {as bs : List A} {a : A} -> (as ⊨-var a) -> (as ⋆ bs ⊨-var a)
  -- ι₁-var {as = .(_ ∷ _)} {bs} zero = zero
  -- ι₁-var {as = .(_ ∷ _)} {bs} (suc i) = suc (ι₁-var i)


  -- ι₂-var-base : ∀{A : 𝒰 𝑘} {bs : List A} {a' a : A} -> (bs ⊨-var a) -> (a' ∷ bs ⊨-var a)
  -- ι₂-var-base zero = suc zero
  -- ι₂-var-base (suc i) = {!!}
  --   -- let r = ι₂-var-base i
  --   -- in {!!}

  -- ι₂-var : ∀{A : 𝒰 𝑘} {as bs : List A} {a : A} -> (bs ⊨-var a) -> (as ⋆ bs ⊨-var a)
  -- ι₂-var zero = {!!}
  -- ι₂-var (suc i) = {!!}

  -- subst↑ : ∀{𝔍s 𝔎} -> 𝔍s ⊩ᶠ↑ 𝔎 -> (∀ {𝔍} -> 𝔍s ⊨-var 𝔍 -> ∑ λ ℑs -> ℑs ⊩ᶠ↑ 𝔍) -> ∑ λ ℑs -> ℑs ⊩ᶠ↑ 𝔎
  -- subst↑ (meta {Γ} {Δ} {α}) σ = σ zero
  -- subst↑ (lam t s) σ =
  --   let _ , t' = subst↑ t (λ x -> σ (ι₁-var x))
  --       _ , s' = subst↑ s (λ x -> σ (ι₂-var x))
  --   in _ , lam t' s'
  -- subst↑ (app t s) σ =
  --   let _ , t' = subst↑ t (λ x -> σ (ι₁-var x))
  --       _ , s' = subst↑ s (λ x -> σ (ι₂-var x))
  --   in _ , app t' s'
  -- subst↑ (con x) σ = _ , con x
  -- subst↑ (var x) σ = _ , var x

  subst↑ : ∀{ℑss 𝔍s 𝔎} -> 𝔍s ⊩ᶠ↑ 𝔎 -> Subs _⊩ᶠ↑_ ℑss 𝔍s -> ∑ λ ℑs -> (join ℑss ≣ ℑs) × (ℑs ⊩ᶠ↑ 𝔎)
  subst↑ meta (x ∷ []) = _ , unit-r-⋆ , x
  subst↑ {ℑss = ℑss} (lam {𝔍 = 𝔍s} {𝔍' = 𝔍s'} t s) σ =
    let Γ₀s , Γ₁s , p , σ₁ , σ₂ = split-Subs {Δ = 𝔍s} {Δ' = 𝔍s'} σ
        Γ₀ , Γ₀s∼Γ₀ , t' = subst↑ t σ₁
        Γ₁ , Γ₁s∼Γ₁ , s' = subst↑ s σ₂

        P : join ℑss ∼ Γ₀ ⋆ Γ₁
        P = join ℑss             ⟨ cong-Str join p ⟩-∼
            join (Γ₀s ⋆ Γ₁s)     ⟨ distr-join-⋆ {xs = Γ₀s} {ys = Γ₁s} ⟩-∼
            join Γ₀s ⋆ join Γ₁s  ⟨ Γ₀s∼Γ₀ ≀⋆≀ Γ₁s∼Γ₁ ⟩-∼
            Γ₀ ⋆ Γ₁              ∎

    in (Γ₀ ⋆ Γ₁) , P , lam t' s'
  subst↑ {ℑss = ℑss} (app {𝔍s = 𝔍s} {𝔍s' = 𝔍s'} t s) σ =
    let Γ₀s , Γ₁s , p , σ₁ , σ₂ = split-Subs {Δ = 𝔍s} {Δ' = 𝔍s'} σ
        Γ₀ , Γ₀s∼Γ₀ , t' = subst↑ t σ₁
        Γ₁ , Γ₁s∼Γ₁ , s' = subst↑ s σ₂

        P : join ℑss ∼ Γ₀ ⋆ Γ₁
        P = join ℑss             ⟨ cong-Str join p ⟩-∼
            join (Γ₀s ⋆ Γ₁s)     ⟨ distr-join-⋆ {xs = Γ₀s} {ys = Γ₁s} ⟩-∼
            join Γ₀s ⋆ join Γ₁s  ⟨ Γ₀s∼Γ₀ ≀⋆≀ Γ₁s∼Γ₁ ⟩-∼
            Γ₀ ⋆ Γ₁              ∎

    in (Γ₀ ⋆ Γ₁) , P , app t' s'
  subst↑ (con x) [] = ⦋⦌ , refl , con x
  subst↑ (var x) [] = ⦋⦌ , refl , var x

  private
    _⇀_ = Hom-Subs _⊩ᶠ↑_

  subst↑-Hom : ∀{ℑs 𝔍s 𝔎s} ->  (ℑs ⇀ 𝔍s) -> (𝔍s ⇀ 𝔎s) -> ℑs ⇀ 𝔎s
  subst↑-Hom σ (.⦋⦌ , refl-≣ , []) = σ
  subst↑-Hom (_ , _ , σ) ((Γ ∷ Γ') , refl-≣ , (x ∷ t)) =
    let Γ₀ , Γ₁ , Γp , σ₀ , σ₁ = split-Subs {Δ = Γ} {Δ' = join Γ'} σ
        _ , x'p , x' = subst↑ x σ₀
        _ , t'p , t' = subst↑-Hom (_ , refl-≣ , σ₁) (_ , refl-≣ , t)

    in {!!} , ({!!} , x' ∷ t')

  id-Subs : ∀{𝔍s} -> 𝔍s ⇀ 𝔍s
  id-Subs {⦋⦌} = [] , (refl , [])
  id-Subs {x ∷ J₁} = {!!} , ({!!} , meta ∷ (id-Subs .snd .snd))

  -- 𝔍s ⊩ᶠ↑ 𝔎 -> Subs _⊩ᶠ↑_ ℑss 𝔍s -> ∑ λ ℑs -> (join ℑss ≣ ℑs) × (ℑs ⊩ᶠ↑ 𝔎)



  _⊩ᶠ'_ : (𝔍s : List (Jdg ⟨ K ⟩)) -> Jdg ⟨ K ⟩ -> 𝒰 (𝑗 ､ 𝑖)
  _⊩ᶠ'_ 𝔍 (αs ⊢ α) = 𝔍 ⊩ᶠ ([] ∣ [] ⇒ (αs ⊢ α))


{-
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
-}


