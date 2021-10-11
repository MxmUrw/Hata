
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.Category where

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
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Cartesian


module _ {K : Kinding 𝑗} {γ : MetaTermCalculus K 𝑖} where
  open MTCDefinitions γ

  Hom-Subs : ∀ ℑs -> ∀ 𝔍s -> 𝒰 _
  Hom-Subs ℑs 𝔍s = Subs _⊩ᶠ↑_ ℑs 𝔍s


  subst↑ : ∀{ℑs 𝔍s 𝔎} -> Subs _⊩ᶠ↑_ ℑs 𝔍s -> 𝔍s ⊩ᶠ↑ 𝔎 -> (ℑs ⊩ᶠ↑ 𝔎)
  subst↑ σ (meta x) = getvar σ x
  subst↑ σ (lam t s) = lam (subst↑ σ t) (subst↑ σ s)
  subst↑ σ (app t s) = app (subst↑ σ t) (subst↑ σ s)
  subst↑ σ (con x) = con x
  subst↑ σ (var x) = var x

  subst↑-Hom : ∀{ℑs 𝔍s 𝔎s} -> Subs _⊩ᶠ↑_ ℑs 𝔍s -> Subs _⊩ᶠ↑_ 𝔍s 𝔎s -> Subs _⊩ᶠ↑_ ℑs 𝔎s
  subst↑-Hom s [] = []
  subst↑-Hom s (x ∷ t) = subst↑ s x ∷ subst↑-Hom s t

  infixl 40 _◆-Subs_
  _◆-Subs_ = subst↑-Hom

  wk-meta : ∀{𝔧 𝔍s 𝔎} -> 𝔍s ⊩ᶠ↑ 𝔎 -> (𝔧 ∷ 𝔍s) ⊩ᶠ↑ 𝔎
  wk-meta (meta x) = meta (suc x)
  wk-meta (lam t s) = lam (wk-meta t) (wk-meta s)
  wk-meta (app t s) = app (wk-meta t) (wk-meta s)
  wk-meta (con x) = con x
  wk-meta (var x) = var x

  wk-meta-Subs : ∀{𝔧 𝔍s 𝔎s} -> Hom-Subs 𝔍s 𝔎s -> Hom-Subs (𝔧 ∷ 𝔍s) 𝔎s
  wk-meta-Subs [] = []
  wk-meta-Subs (x ∷ s) = wk-meta x ∷ wk-meta-Subs s


  id-Subs : ∀{𝔍s} -> Hom-Subs 𝔍s 𝔍s
  id-Subs {⦋⦌} = []
  id-Subs {x ∷ J} = meta zero ∷ wk-meta-Subs (id-Subs)

  instance
    isSetoid:Hom-Subs : ∀{a b} -> isSetoid (Hom-Subs a b)
    isSetoid:Hom-Subs = isSetoid:byStrId

  instance
    isSetoid:⊩ᶠ↑ : ∀{a b} -> isSetoid (a ⊩ᶠ↑ b)
    isSetoid:⊩ᶠ↑ = isSetoid:byStrId


  wk-getvar-comm : ∀{a b c d} -> {σ : Hom-Subs a b} {x : b ⊨-var c} -> getvar (wk-meta-Subs {d} σ) x ≣ wk-meta (getvar σ x)
  wk-getvar-comm {σ = x₁ ∷ σ} {x = zero} = refl-≣
  wk-getvar-comm {σ = x₁ ∷ σ} {x = suc x} = wk-getvar-comm {σ = σ} {x = x}

  unit-l-var : ∀{a b} -> {x : a ⊨-var b} -> getvar id-Subs x ≣ meta x
  unit-l-var {x = zero} = refl-≣
  unit-l-var {a = a} {x = suc x} =
    let p = wk-getvar-comm {σ = id-Subs} {x = x}
    in p ∙ (cong-Str wk-meta unit-l-var)


  unit-l-subst : ∀{a b} -> {t : a ⊩ᶠ↑ b} -> subst↑ id-Subs t ≣ t
  unit-l-subst {t = meta x} = unit-l-var
  unit-l-subst {t = lam t s} = cong₂-Str lam unit-l-subst unit-l-subst
  unit-l-subst {t = app t s} = cong₂-Str app unit-l-subst unit-l-subst
  unit-l-subst {t = con x} = refl-≣
  unit-l-subst {t = var x} = refl-≣

  unit-l-Subs : ∀{a b} -> {f : Hom-Subs a b} -> id-Subs ◆-Subs f ∼ f
  unit-l-Subs {a} {.⦋⦌} {f = []} = refl
  unit-l-Subs {a} {.(_ ∷ _)} {f = x ∷ f} = cong₂-Str _∷_ (unit-l-subst) (unit-l-Subs)

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




