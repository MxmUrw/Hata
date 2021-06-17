
module Verification.Experimental.Theory.Std.Specific.Simple.MetaTermCalculus.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Category.Std.Category.Definition

module _ (MetaKind : 𝒰₀) where
  -- data TermConConditionType : 𝒰₀ where
  --   _⇒_ : List MetaKind -> MetaKind -> TermConConditionType

  data TermConType : 𝒰₀ where
    _⇒_ : List MetaKind -> MetaKind -> TermConType

data SimpleCtx (A : 𝒰 𝑖) : 𝒰 𝑖 where
  [] : SimpleCtx A
  _,_ : SimpleCtx A -> A -> SimpleCtx A

module _ {A : 𝒰 𝑖} where
  data π-Ctx : (Γ : SimpleCtx A) (a : A) -> 𝒰 𝑖 where
    zero : ∀{Γ a} -> π-Ctx (Γ , a) a
    suc : ∀{Γ a b} -> π-Ctx Γ a -> π-Ctx (Γ , b) a

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-SimpleCtx : (f : A -> B) -> SimpleCtx A -> SimpleCtx B
  map-SimpleCtx f = {!!}


module MTC where
  record Signature : 𝒰₁ where
    field MetaKind : 𝒰₀
    field TermCon : SimpleCtx (TermConType MetaKind) -> MetaKind -> 𝒰₀

  open Signature

  module _ (σ : Signature) where

    --- basic definitions

    data Type : 𝒰₀ where
      kind : MetaKind σ -> Type
      _⇒_ : Type -> Type -> Type


    ⟦_⟧-Con : TermConType (MetaKind σ) -> Type
    ⟦ [] ⇒ β ⟧-Con       = kind β
    ⟦ (x ∷ as) ⇒ β ⟧-Con = {!!}

    Ctx = SimpleCtx Type


    --- σ structures
    --- i.e., a category and an interpretation of the kinds and constructors of σ
    record ProductStructure (𝒞 : Category 𝑖) : 𝒰 𝑖 where
      -- field 


    --- σ terms

    data [_]_⊢_ (Meta : SimpleCtx (TermConType (MetaKind σ)) -> MetaKind σ -> 𝒰₀) : Ctx -> Type -> 𝒰₀ where
      meta : ∀{Γ τ} -> (Meta Γ τ)     -> [ Meta ] (map-SimpleCtx ⟦_⟧-Con Γ) ⊢ kind τ
      con : ∀{Γ τ} -> (TermCon σ Γ τ) -> [ Meta ] (map-SimpleCtx ⟦_⟧-Con Γ) ⊢ kind τ
      var : ∀{Γ τ} -> (π-Ctx Γ τ) -> [ Meta ] Γ ⊢ τ
      lam : ∀{Γ α β} -> [ Meta ] (Γ , α) ⊢ β -> [ Meta ] Γ ⊢ (α ⇒ β)
      app : ∀{Γ α β} -> [ Meta ] Γ ⊢ (α ⇒ β) -> [ Meta ] Γ ⊢ α -> [ Meta ] Γ ⊢ β








