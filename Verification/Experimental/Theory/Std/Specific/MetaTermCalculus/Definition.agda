

module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple

data MetaSort : 𝒰₀ where
  main var : MetaSort

module _ (K : 𝒰 𝑖) where
  --- basic definitions

  data Type-MTC : 𝒰 𝑖 where
    kind : K -> Type-MTC
    _⇒_ : Type-MTC -> Type-MTC -> Type-MTC

  infixr 30 _⇒_

data MetaJ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  _◀_ : Jdg-⦿ A -> MetaSort -> MetaJ A

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-MetaJ : (f : A -> B) -> MetaJ A -> MetaJ B
  map-MetaJ f (x ◀ s) = map-Jdg-⦿ f x ◀ s

-----------------------------------
-- ==* MTC signatures


record MetaTermCalculus (𝑖 : 𝔏 ^ 2): 𝒰 (𝑖 ⁺) where
  field MetaKind : 𝒰 (𝑖 ⌄ 0)
  -- field varzero : MetaKind
  field ∂ₘᵇ : MetaKind -> MetaKind
  -- field isGoodType : Type' MetaKind -> 𝒰₀
  field isHiddenMeta : Jdg-⦿ (Type-MTC MetaKind) -> 𝒰 (𝑖 ⌄ 0)
  field TermCon : (τ : Rule-⦿ MetaKind) -> 𝒰 (𝑖)
  ∂ₘ : Type-MTC MetaKind -> Type-MTC MetaKind
  ∂ₘ (kind x) = kind (∂ₘᵇ x)
  ∂ₘ (a ⇒ b) = a ⇒ (∂ₘ b)

open MetaTermCalculus public

macro
  MTC : ∀ 𝑖 -> SomeStructure
  MTC 𝑖 = #structureOn (MetaTermCalculus 𝑖)

module _ (A B : MTC 𝑖) where
  record isHom-MTC (f : MetaKind A -> MetaKind B) : 𝒰 𝑖 where
    -- field map-varzero : f (varzero A) ≡ varzero B
    -- field map-varsuc : f (varsuc A) ≡ varsuc B
    field map-TermCon : ∀ ρ -> TermCon A ρ -> TermCon B (map f ρ)
  Hom-MTC = _ :& isHom-MTC


instance
  isCategory:MTC : isCategory (MetaTermCalculus 𝑖)
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



module MTCDefinitions (σ : MetaTermCalculus 𝑖) where

  --- basic definitions
  private
    Type = Type-MTC (MetaKind σ)
    K = MetaKind σ


  -- ⟦_⟧-Con : TermConType (MetaKind σ) -> Type
  -- ⟦ [] ⇒ β ⟧-Con       = kind β
  -- ⟦ (x ∷ as) ⇒ β ⟧-Con = {!!}

  -- Ctx = SCtx Type

  module _ {J K : 𝒰 𝑗} where
    arrify : (f : J -> Type-MTC K) -> Ctx-⦿ J -> Type-MTC K -> Type-MTC K
    arrify f [] = λ α -> α
    arrify f (Γ ,, α) = λ β -> arrify f Γ (f α ⇒ β)

  ⟦_⟧-J : Jdg-⦿ K -> Type-MTC K
  ⟦_⟧-J (Γ ⊢ α) = arrify kind Γ (kind α)

  ⟦_⟧-R : Rule-⦿ K -> Type-MTC K
  ⟦_⟧-R (𝔧s ⊩ 𝔦) = arrify ⟦_⟧-J 𝔧s (⟦_⟧-J 𝔦)

  arrify-J-kind : ∀{Γ α β} -> ⟦ Γ ⊢ α ⟧-J ≣ kind β -> (Γ ≣ []) ∧ (α ≣ β)
  arrify-J-kind {G} {a} {b} p = {!!}

  arrify-J-split : ∀{Γ α β τ} -> ⟦ Γ ⊢ τ ⟧-J ≣ (α ⇒ β) -> ∑ λ Γ' -> ∑ λ α' -> (α ≣ kind α') ∧ (Γ ≣ ([] ,, α') ⋆ Γ') ∧ (⟦ Γ' ⊢ τ ⟧-J ≣ β)
  arrify-J-split = ?

  MetaJ'  = Jdg-⦿ (Type-MTC (MetaKind σ))

  data OptMeta (𝔧 : MetaJ') (Opt : MetaJ' -> 𝒰 𝑗) (Fam : MetaJ' -> 𝒰 𝑘) : 𝒰 (𝑗 ､ 𝑘) where
    skip : Opt 𝔧 -> OptMeta 𝔧 Opt Fam
    give : Fam 𝔧 -> (¬ Opt 𝔧) -> OptMeta 𝔧 Opt Fam



  data _⊩ᶠ_ (Μ : Ctx-⦿ (Jdg-⦿ (Type-MTC (MetaKind σ)))) : MetaJ (Type-MTC (MetaKind σ)) -> 𝒰 𝑖 where
    meta : ∀{𝔧} -> OptMeta 𝔧 (isHiddenMeta σ) (Μ ⊢-Ctx-⦿_) -> Μ ⊩ᶠ (𝔧 ◀ main)
    var : ∀{Γ τ} -> (Μ ⊩ᶠ (Γ ⊢ τ ◀ var)) -> Μ ⊩ᶠ (Γ ⊢ τ ◀ main)
    con :  ∀{Γ τ τ'} -> (⟦ τ ⟧-R ≣ τ') -> (TermCon σ τ) -> Μ ⊩ᶠ (Γ ⊢ τ' ◀ main)
    lam : ∀{Γ α β} -> Μ ⊩ᶠ ((Γ ,, α) ⊢ β ◀ main) -> Μ ⊩ᶠ (Γ ⊢ (α ⇒ β) ◀ main)
    app : ∀{Γ α β} -> Μ ⊩ᶠ (Γ ⊢ (α ⇒ β) ◀ main) -> Μ ⊩ᶠ (Γ ⊢ α ◀ main) -> Μ ⊩ᶠ (Γ ⊢ β ◀ main)

    suc  : ∀{Γ α β} -> Μ ⊩ᶠ (Γ ⊢ ∂ₘ σ α ◀ main)  -> Μ ⊩ᶠ (Γ ⊢ β ◀ var) -> Μ ⊩ᶠ ((Γ ,, α) ⊢ β ◀ var)
    zero : ∀{Γ α}   -> Μ ⊩ᶠ (Γ ⊢ ∂ₘ σ α ◀ main) -> Μ ⊩ᶠ ((Γ ,, α) ⊢ α ◀ var)




  mutual
    data _⊩ᶠ↓-app_ (Μ : Ctx-⦿ (Jdg-⦿ (Type-MTC (MetaKind σ)))) : MetaJ (Type-MTC (MetaKind σ)) -> 𝒰 𝑖 where
      app : ∀{Γ α β} -> Μ ⊩ᶠ↓-app (Γ ⊢ (α ⇒ β) ◀ main) -> Μ ⊩ᶠ↓ (Γ ⊢ α ◀ main) -> Μ ⊩ᶠ↓-app (Γ ⊢ β ◀ main)
      var : ∀{Γ τ} -> (Μ ⊩ᶠ↓ (Γ ⊢ τ ◀ var)) -> Μ ⊩ᶠ↓-app (Γ ⊢ τ ◀ main)
      con :  ∀{Γ τ τ'} -> ⟦ τ ⟧-R ≣ τ' -> (TermCon σ τ) -> Μ ⊩ᶠ↓-app (Γ ⊢ τ' ◀ main)
      meta : ∀{𝔧} -> OptMeta 𝔧 (isHiddenMeta σ) (Μ ⊢-Ctx-⦿_) -> Μ ⊩ᶠ↓-app (𝔧 ◀ main)
      -- meta : ∀{𝔧} -> OptMeta 𝔧 (isHiddenMeta σ) (Μ ⊢-Ctx-⦿_) -> Μ ⊩ᶠ 𝔧


    data _⊩ᶠ↓_ (Μ : Ctx-⦿ (Jdg-⦿ (Type-MTC (MetaKind σ)))) : MetaJ (Type-MTC (MetaKind σ)) -> 𝒰 𝑖 where
      lam : ∀{Γ α β} -> Μ ⊩ᶠ↓ ((Γ ,, α) ⊢ β ◀ main) -> Μ ⊩ᶠ↓ (Γ ⊢ (α ⇒ β) ◀ main)
      getapp : ∀{Γ α s} -> Μ ⊩ᶠ↓-app (Γ ⊢ kind α ◀ s) -> Μ ⊩ᶠ↓ (Γ ⊢ kind α ◀ s)

      suc  : ∀{Γ α β} -> Μ ⊩ᶠ↓ (Γ ⊢ ∂ₘ σ α ◀ main)  -> Μ ⊩ᶠ↓ (Γ ⊢ β ◀ var) -> Μ ⊩ᶠ↓ ((Γ ,, α) ⊢ β ◀ var)
      zero : ∀{Γ α}   -> Μ ⊩ᶠ↓ (Γ ⊢ ∂ₘ σ α ◀ main) -> Μ ⊩ᶠ↓ ((Γ ,, α) ⊢ α ◀ var)

    _⊩ᶠ↓'_ : (Μ : Ctx-⦿ (Jdg-⦿ (Type-MTC (MetaKind σ)))) -> MetaJ' -> 𝒰 𝑖
    _⊩ᶠ↓'_ a b = _⊩ᶠ↓_ a (b ◀ main)


record Ctx-MTC (γ : MetaTermCalculus 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  constructor incl
  field ⟨_⟩ : (Ctx-⦿ (Jdg-⦿ (MetaKind γ)))
open Ctx-MTC {{...}} public

module _ {γ : MetaTermCalculus 𝑖} where
  open MTCDefinitions γ

  -- instance
  --   isCategory:Ctx-MTC : isCategory (Ctx-⦿ (MetaJ (MetaKind γ)))
  --   isCategory.Hom isCategory:Ctx-MTC = Sub-⦿ (_⊩ᶠ↓_)

  instance
    isCategory:Ctx-MTC : isCategory (Ctx-MTC γ)
    isCategory.Hom isCategory:Ctx-MTC = λ A B -> Sub-⦿ (_⊩ᶠ↓'_) (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ A ⟩) (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ B ⟩)
    isCategory.isSetoid:Hom isCategory:Ctx-MTC = isSetoid:byPath
    isCategory.id isCategory:Ctx-MTC = {!!}
    isCategory._◆_ isCategory:Ctx-MTC = {!!}
    isCategory.unit-l-◆ isCategory:Ctx-MTC = {!!}
    isCategory.unit-r-◆ isCategory:Ctx-MTC = {!!}
    isCategory.unit-2-◆ isCategory:Ctx-MTC = {!!}
    isCategory.assoc-l-◆ isCategory:Ctx-MTC = {!!}
    isCategory.assoc-r-◆ isCategory:Ctx-MTC = {!!}
    isCategory._◈_ isCategory:Ctx-MTC = {!!}

    isMonoidal:Ctx-MTC : isMonoidal ′ Ctx-MTC γ ′
    isMonoidal:Ctx-MTC = {!!}

  instance
    isCwJ:Ctx-MTC : hasJudgements ′ Ctx-MTC γ ′
    isCwJ:Ctx-MTC = record { JKind = (MetaKind γ) ; JObj = λ 𝔧 -> {!!} } -- incl ([] ,, ([] ⊢ ⟦ 𝔧 ⟧-J ◀ main)) }


  --   isMonoidal:Ctx-MTC : isMonoidal ′ Ctx-⦿ (MetaJ (MetaKind γ)) ′
  --   isMonoidal:Ctx-MTC = {!!}

  -- instance
  --   isCwJ:Ctx-MTC : hasJudgements ′ Ctx-⦿ (MetaJ (MetaKind γ)) ′
  --   isCwJ:Ctx-MTC = record { JKind = (MetaKind γ) ; JObj = λ 𝔧 -> [] ,, ([] ⊢ ⟦ 𝔧 ⟧-J ◀ main) }

{-
-}
      -- suc  : ∀{Γ α β} -> Μ ⊩ᶠ (Γ ⊢ β ◀ var) -> Μ ⊩ᶠ ((Γ ,, α) ⊢ β ◀ var)
      -- zero : ∀{Γ α}   -> Μ ⊩ᶠ ((Γ ,, α) ⊢ α ◀ var)


    -- data [_]_⊢_ (Μ : SCtx MetaVar) : Ctx -> Type -> 𝒰₀ where
      -- meta : ∀{Γ τ} -> (Μ Γ τ)     -> [ Μ ] (map-SCtx kind Γ) ⊢ kind τ
      -- con : ∀{Γ τ} -> (TermCon σ Γ τ) -> [ Μ ] (map-SCtx ⟦_⟧-Con Γ) ⊢ kind τ
      -- var : ∀{Γ τ} -> (π-Ctx Γ τ) -> (π-Ctx Μ (Γ ⊢ τ , var)) -> [ Μ ] Γ ⊢ τ
      -- lam : ∀{Γ α β} -> [ Μ ] (Γ ,, α) ⊢ β -> [ Μ ] Γ ⊢ (α ⇒ β)
      -- app : ∀{Γ α β} -> [ Μ ] Γ ⊢ (α ⇒ β) -> [ Μ ] Γ ⊢ α -> [ Μ ] Γ ⊢ β





















{-


-- module _ (MetaKind : 𝒰₀) where
  -- data TermConConditionType : 𝒰₀ where
  --   _⇒_ : List MetaKind -> MetaKind -> TermConConditionType

  -- data TermConType : 𝒰₀ where
  --   _⇒_ : List MetaKind -> MetaKind -> TermConType

data MetaSort : 𝒰₀ where
  main var special : MetaSort

module _ (K : 𝒰₀) where
  --- basic definitions

  data Type-MTC : 𝒰₀ where
    kind : K -> Type-MTC
    _⇒_ : Type-MTC -> Type-MTC -> Type-MTC

  infixr 30 _⇒_

  data MetaJ : 𝒰₀ where
    _◀_ : Judgement (SCtx Type-MTC) Type-MTC -> MetaSort -> MetaJ

  data isKindSCtx : SCtx Type-MTC -> 𝒰₀ where
    [] : isKindSCtx []
    _,,_ : ∀ k {Γ} -> isKindSCtx Γ -> isKindSCtx (Γ ,, kind k)

  data isKindMetaJ : MetaJ -> 𝒰₀ where
    _◀_ : ∀{Γ} -> isKindSCtx Γ -> ∀ k s -> isKindMetaJ (Γ ⊢ kind k ◀ s)

  KindMetaJ = ∑ isKindMetaJ

  data isConArg : Type-MTC -> 𝒰₀ where
    kind : ∀ k -> isConArg (kind k)
    _⇒_ : ∀ k {a} -> isConArg a -> isConArg (kind k ⇒ a)

  data isConType : Type-MTC -> 𝒰₀ where
    kind : ∀ k -> isConType (kind k)
    _⇒_ : ∀ {a t} -> isConArg a -> isConType t -> isConType (a ⇒ t)


record MetaTermCalculus : 𝒰₁ where
  field MetaKind : 𝒰₀
  field varzero : MetaKind
  field varsuc : MetaKind
  field isGoodType : Type-MTC MetaKind -> 𝒰₀
  field isHiddenMeta : MetaJ MetaKind -> 𝒰₀
  field TermCon : (τ : Type-MTC MetaKind) -> isGoodType τ -> 𝒰₀

open MetaTermCalculus




-}


