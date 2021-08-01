
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition


module _ {K : Kinding 𝑗} {γ : MetaTermCalculus K 𝑖} where
  open MTCDefinitions γ

  Hom-Subs : ∀ (ℑs 𝔍s : List (Jdg₂ ⟨ K ⟩)) -> 𝒰 _
  Hom-Subs ℑs 𝔍s = Subs _⊩ᶠ-pat_ ℑs 𝔍s


  mutual
    subst-patlam : ∀{ℑs 𝔍s 𝔎} -> Subs _⊩ᶠ-pat_ ℑs 𝔍s -> 𝔍s ⊩ᶠ-patlam 𝔎 -> (ℑs ⊩ᶠ-patlam 𝔎)
    subst-patlam σ (lam ts) = lam (subst-pat σ ts)

    subst-pat : ∀{ℑs 𝔍s 𝔎} -> Subs _⊩ᶠ-pat_ ℑs 𝔍s -> 𝔍s ⊩ᶠ-pat 𝔎 -> (ℑs ⊩ᶠ-pat 𝔎)
    subst-pat σ (app-meta M s) =
      let N = getvar σ M
      in apply-injVars N s
    subst-pat σ (app-var v ts) = app-var v (λ x → subst-patlam σ (ts x))
    subst-pat σ (app-con c ts) = app-con c (λ x -> subst-patlam σ (ts x))


  subst-pat-Hom : ∀{ℑs 𝔍s 𝔎s} -> Subs _⊩ᶠ-pat_ ℑs 𝔍s -> Subs _⊩ᶠ-pat_ 𝔍s 𝔎s -> Subs _⊩ᶠ-pat_ ℑs 𝔎s
  subst-pat-Hom s [] = []
  subst-pat-Hom s (x ∷ t) = subst-pat s x ∷ subst-pat-Hom s t

  infixl 40 _◆-Subs_
  _◆-Subs_ = subst-pat-Hom

  mutual
    wk-meta-lam : ∀{𝔧 𝔍s 𝔎} -> 𝔍s ⊩ᶠ-patlam 𝔎 -> (𝔧 ∷ 𝔍s) ⊩ᶠ-patlam 𝔎
    wk-meta-lam (lam t) = lam (wk-meta t)

    wk-meta : ∀{𝔧 𝔍s 𝔎} -> 𝔍s ⊩ᶠ-pat 𝔎 -> (𝔧 ∷ 𝔍s) ⊩ᶠ-pat 𝔎
    wk-meta (app-meta M s) = app-meta (suc M) s
    wk-meta (app-var c ts) = app-var c (λ x -> (wk-meta-lam (ts x)))
    wk-meta (app-con c ts) = app-con c (λ x -> (wk-meta-lam (ts x)))


  wk-meta-Subs : ∀{𝔧 𝔍s 𝔎s} -> Hom-Subs 𝔍s 𝔎s -> Hom-Subs (𝔧 ∷ 𝔍s) 𝔎s
  wk-meta-Subs [] = []
  wk-meta-Subs (x ∷ s) = wk-meta x ∷ wk-meta-Subs s


  id-Subs : ∀{𝔍s} -> Hom-Subs 𝔍s 𝔍s
  id-Subs {⦋⦌} = []
  id-Subs {x ∷ J} = app-meta zero id ∷ wk-meta-Subs (id-Subs)

  instance
    isSetoid:Hom-Subs : ∀{a b} -> isSetoid (Hom-Subs a b)
    isSetoid:Hom-Subs = isSetoid:byPath

  instance
    isSetoid:⊩ᶠ-pat : ∀{a b} -> isSetoid (a ⊩ᶠ-pat b)
    isSetoid:⊩ᶠ-pat = isSetoid:byPath


{-
  wk-getvar-comm : ∀{a b c d} -> {σ : Hom-Subs a b} {x : b ⊨-var c} -> getvar (wk-meta-Subs {d} σ) x ≣ wk-meta (getvar σ x)
  wk-getvar-comm {σ = x₁ ∷ σ} {x = zero} = refl-≣
  wk-getvar-comm {σ = x₁ ∷ σ} {x = suc x} = wk-getvar-comm {σ = σ} {x = x}

  unit-l-var : ∀{a b} -> {x : a ⊨-var b} -> getvar id-Subs x ≣ meta x
  unit-l-var {x = zero} = refl-≣
  unit-l-var {a = a} {x = suc x} =
    let p = wk-getvar-comm {σ = id-Subs} {x = x}
    in p ∙ (cong-Str wk-meta unit-l-var)


-}

  private
    lem-10 : ∀{Γ Δ a α} (M : a ⊨-var Δ ⇒ α) (s : injvars Γ ⟶ injvars Δ)
           -> apply-injVars (getvar id-Subs M) s ≡ app-meta M s
    lem-10 zero s = {!!}
    lem-10 (suc M) s = {!!}



  mutual
    unit-l-subst-lam : ∀{a b} -> {t : a ⊩ᶠ-patlam b} -> subst-patlam id-Subs t ≡ t
    unit-l-subst-lam {t = lam s} = cong lam unit-l-subst

    unit-l-subst : ∀{a b} -> {t : a ⊩ᶠ-pat b} -> subst-pat id-Subs t ≡ t
    unit-l-subst {t = app-meta M s} = lem-10 M s
    unit-l-subst {t = app-var c ts} = cong₂ app-var refl-≡ (λ i x -> unit-l-subst-lam {t = ts x} i)
    unit-l-subst {t = app-con c ts} = cong₂ app-con refl-≡ (λ i x -> unit-l-subst-lam {t = ts x} i)
  -- unit-l-subst {t = meta x} = unit-l-var
  -- unit-l-subst {t = lam t s} = cong₂-Str lam unit-l-subst unit-l-subst
  -- unit-l-subst {t = app t s} = cong₂-Str app unit-l-subst unit-l-subst
  -- unit-l-subst {t = con x} = refl-≣
  -- unit-l-subst {t = var x} = refl-≣

  unit-l-Subs : ∀{a b} -> {f : Hom-Subs a b} -> id-Subs ◆-Subs f ∼ f
  unit-l-Subs {f = []} = refl
  unit-l-Subs {f = x ∷ f} = cong₂ _∷_ unit-l-subst unit-l-Subs

module _ {K : Kinding 𝑗} where
  record MTCSubs (γ : MetaTermCalculus K 𝑖) : 𝒰 𝑗 where
    field ⟨_⟩ : List (Jdg₂ ⟨ K ⟩)

  open MTCSubs public

module _ {K : Kinding 𝑗} {γ : MetaTermCalculus K 𝑖} where
  instance
    isCategory:Subs : isCategory (MTCSubs γ)
    isCategory.Hom isCategory:Subs           = λ a b -> Hom-Subs {γ = γ} ⟨ b ⟩ ⟨ a ⟩
    isCategory.isSetoid:Hom isCategory:Subs  = isSetoid:Hom-Subs
    isCategory.id isCategory:Subs            = id-Subs
    isCategory._◆_ isCategory:Subs           = λ f g -> g ◆-Subs f
    isCategory.unit-l-◆ isCategory:Subs      = {!!}
    isCategory.unit-r-◆ isCategory:Subs      = unit-l-Subs
    isCategory.unit-2-◆ isCategory:Subs      = {!!}
    isCategory.assoc-l-◆ isCategory:Subs     = {!!}
    isCategory.assoc-r-◆ isCategory:Subs     = {!!}
    isCategory._◈_ isCategory:Subs           = {!!}





