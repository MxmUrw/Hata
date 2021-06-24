
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Theory.Std.TypeTheory.Definition

-- module _ (MetaKind : 𝒰₀) where
  -- data TermConConditionType : 𝒰₀ where
  --   _⇒_ : List MetaKind -> MetaKind -> TermConConditionType

  -- data TermConType : 𝒰₀ where
  --   _⇒_ : List MetaKind -> MetaKind -> TermConType

data MetaSort : 𝒰₀ where
  main var special : MetaSort

module _ (K : 𝒰₀) where
  --- basic definitions

  data Type' : 𝒰₀ where
    kind : K -> Type'
    _⇒_ : Type' -> Type' -> Type'

  infixr 30 _⇒_

  data MetaJ : 𝒰₀ where
    _◀_ : Judgement (SCtx Type') Type' -> MetaSort -> MetaJ

  data isKindSCtx : SCtx Type' -> 𝒰₀ where
    [] : isKindSCtx []
    _,,_ : ∀ k {Γ} -> isKindSCtx Γ -> isKindSCtx (Γ ,, kind k)

  data isKindMetaJ : MetaJ -> 𝒰₀ where
    _◀_ : ∀{Γ} -> isKindSCtx Γ -> ∀ k s -> isKindMetaJ (Γ ⊢ kind k ◀ s)

  KindMetaJ = ∑ isKindMetaJ

  data isConArg : Type' -> 𝒰₀ where
    kind : ∀ k -> isConArg (kind k)
    _⇒_ : ∀ k {a} -> isConArg a -> isConArg (kind k ⇒ a)

  data isConType : Type' -> 𝒰₀ where
    kind : ∀ k -> isConType (kind k)
    _⇒_ : ∀ {a t} -> isConArg a -> isConType t -> isConType (a ⇒ t)


module MTC where
  record Signature : 𝒰₁ where
    field MetaKind : 𝒰₀
    field varzero : MetaKind
    field varsuc : MetaKind
    field isGoodType : Type' MetaKind -> 𝒰₀
    field isHiddenMeta : MetaJ MetaKind -> 𝒰₀
    field TermCon : (τ : Type' MetaKind) -> isGoodType τ -> 𝒰₀

  open Signature

  module Definitions (σ : Signature) where

    --- basic definitions
    Type = Type' (MetaKind σ)


    -- ⟦_⟧-Con : TermConType (MetaKind σ) -> Type
    -- ⟦ [] ⇒ β ⟧-Con       = kind β
    -- ⟦ (x ∷ as) ⇒ β ⟧-Con = {!!}

    Ctx = SCtx Type

    MetaJ'  = MetaJ (MetaKind σ)

    data OptMeta (𝔧 : MetaJ') (Opt : MetaJ' -> 𝒰₀) (Fam : MetaJ' -> 𝒰₀) : 𝒰₀ where
      skip : Opt 𝔧 -> OptMeta 𝔧 Opt Fam
      give : Fam 𝔧 -> (¬ Opt 𝔧) -> OptMeta 𝔧 Opt Fam



    appendCon : ∀{Γ} -> isKindSCtx (MetaKind σ) Γ -> ∀{τ} -> isConType (MetaKind σ) τ -> Judgement (SCtx (KindMetaJ (MetaKind σ))) (KindMetaJ (MetaKind σ))
    appendCon Γ (kind k) = [] ⊢ (_ , {!!})
    appendCon G (x ⇒ t) = {!!}

    --- σ structures
      --- i.e., a category and an interpretation of the kinds and constructors of σ
    record Structure (𝒞 : Category 𝑖) : 𝒰 𝑖 where
      field interp-Type : ∀{Μ} -> isKindMetaJ (MetaKind σ) Μ -> ⟨ 𝒞 ⟩
      -- field interp-Con : ∀{Γ τ τp} -> TermCon σ τ τp -> 





    data _⊩_ (Μ : (MetaJ (MetaKind σ)) -> 𝒰₀) : MetaJ (MetaKind σ) -> 𝒰₀ where
      meta : ∀{𝔧} -> OptMeta 𝔧 (isHiddenMeta σ) (Μ) -> Μ ⊩ 𝔧
      var : ∀{Γ τ} -> (Μ ⊩ (Γ ⊢ τ ◀ var)) -> Μ ⊩ (Γ ⊢ τ ◀ main)
      con :  ∀{Γ τ τp} -> (TermCon σ τ τp) -> Μ ⊩ (Γ ⊢ τ ◀ main)
      lam : ∀{Γ α β} -> Μ ⊩ ((Γ ,, α) ⊢ β ◀ main) -> Μ ⊩ (Γ ⊢ (α ⇒ β) ◀ main)
      app : ∀{Γ α β} -> Μ ⊩ (Γ ⊢ (α ⇒ β) ◀ main) -> Μ ⊩ (Γ ⊢ α ◀ main) -> Μ ⊩ (Γ ⊢ β ◀ main)

      suc  : ∀{Γ α β} -> Μ ⊩ (Γ ⊢ kind (varsuc σ) ◀ special)  -> Μ ⊩ (Γ ⊢ β ◀ var) -> Μ ⊩ ((Γ ,, α) ⊢ β ◀ var)
      zero : ∀{Γ α}   -> Μ ⊩ (Γ ⊢ kind (varzero σ) ◀ special) -> Μ ⊩ ((Γ ,, α) ⊢ α ◀ var)






{-
    mutual
      data _⊩↓-app_ (Μ : SCtx (MetaJ (MetaKind σ))) : MetaJ (MetaKind σ) -> 𝒰₀ where
        app : ∀{Γ α β} -> Μ ⊩↓-app (Γ ⊢ (α ⇒ β) ◀ main) -> Μ ⊩↓ (Γ ⊢ α ◀ main) -> Μ ⊩↓-app (Γ ⊢ β ◀ main)
        var : ∀{Γ τ} -> (Μ ⊩↓ (Γ ⊢ τ ◀ var)) -> Μ ⊩↓-app (Γ ⊢ τ ◀ main)
        con :  ∀{Γ τ τp} -> (TermCon σ τ τp) -> Μ ⊩↓-app (Γ ⊢ τ ◀ main)
        meta : ∀{𝔧} -> OptMeta 𝔧 (isHiddenMeta σ) (Μ ⊢̌_) -> Μ ⊩↓-app 𝔧


      data _⊩↓_ (Μ : SCtx (MetaJ (MetaKind σ))) : MetaJ (MetaKind σ) -> 𝒰₀ where
        lam : ∀{Γ α β} -> Μ ⊩↓ ((Γ ,, α) ⊢ β ◀ main) -> Μ ⊩↓ (Γ ⊢ (α ⇒ β) ◀ main)
        getapp : ∀{Γ α s} -> Μ ⊩↓-app (Γ ⊢ kind α ◀ s) -> Μ ⊩↓ (Γ ⊢ kind α ◀ s)

        suc  : ∀{Γ α β} -> Μ ⊩↓ (Γ ⊢ kind (varsuc σ) ◀ special)  -> Μ ⊩↓ (Γ ⊢ β ◀ var) -> Μ ⊩↓ ((Γ ,, α) ⊢ β ◀ var)
        zero : ∀{Γ α}   -> Μ ⊩↓ (Γ ⊢ kind (varzero σ) ◀ special) -> Μ ⊩↓ ((Γ ,, α) ⊢ α ◀ var)
-}


      -- suc  : ∀{Γ α β} -> Μ ⊩ (Γ ⊢ β ◀ var) -> Μ ⊩ ((Γ ,, α) ⊢ β ◀ var)
      -- zero : ∀{Γ α}   -> Μ ⊩ ((Γ ,, α) ⊢ α ◀ var)


    -- data [_]_⊢_ (Μ : SCtx MetaVar) : Ctx -> Type -> 𝒰₀ where
      -- meta : ∀{Γ τ} -> (Μ Γ τ)     -> [ Μ ] (map-SCtx kind Γ) ⊢ kind τ
      -- con : ∀{Γ τ} -> (TermCon σ Γ τ) -> [ Μ ] (map-SCtx ⟦_⟧-Con Γ) ⊢ kind τ
      -- var : ∀{Γ τ} -> (π-Ctx Γ τ) -> (π-Ctx Μ (Γ ⊢ τ , var)) -> [ Μ ] Γ ⊢ τ
      -- lam : ∀{Γ α β} -> [ Μ ] (Γ ,, α) ⊢ β -> [ Μ ] Γ ⊢ (α ⇒ β)
      -- app : ∀{Γ α β} -> [ Μ ] Γ ⊢ (α ⇒ β) -> [ Μ ] Γ ⊢ α -> [ Μ ] Γ ⊢ β








