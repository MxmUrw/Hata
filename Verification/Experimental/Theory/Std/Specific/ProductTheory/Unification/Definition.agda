
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Unification.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Variant.Base.Definition

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition



record ProductTheory (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  field Sort : 𝒰 𝑖
  field {{isDiscrete:Sort}} : isDiscrete Sort
  field {{isSet-Str:Sort}} : isSet-Str Sort
  field Con : List Sort -> Sort -> 𝒰 𝑖
  field {{isDiscrete:Con}} : ∀{αs α} -> isDiscrete (Con αs α)
open ProductTheory public

module _ (𝑖 : 𝔏) where
  macro 𝕋× = #structureOn (ProductTheory 𝑖)

  𝒜 = ProductTheory 𝑖

Type-𝕋× : ProductTheory 𝑖 -> 𝒰 𝑖
Type-𝕋× a = Sort a






-- record FinAxProductTheory (A : 𝒰₀) : 𝒰₀ where
--   field sizeFinAx : ℕ
--   field names : Fin-R sizeFinAx -> String
--   field types : Fin-R sizeFinAx -> (List A ×-𝒰 A)

-- open FinAxProductTheory public



--   -- lookup : (xs : List A) -> (i : 𝔽ʳ (size xs)) -> A
--   -- lookup xs i = ?

-- inList : {A : 𝒰₀} (p : FinAxProductTheory A) -> (List A ×-𝒰 A) -> 𝒰₀
-- inList p xs = ∑ λ (i : Fin-R (sizeFinAx p)) -> types p i ≣ xs



-- makeProductTheory : ∀{A : 𝒰₀} -> FinAxProductTheory A -> ProductTheory ℓ₀
-- Sort (makeProductTheory {A} t) = A
-- isDiscrete:Sort (makeProductTheory t) = {!!}
-- isSet-Str:Sort (makeProductTheory t) = {!!}
-- Con (makeProductTheory t) = λ xs x → inList t (xs , x)
-- isDiscrete:Con (makeProductTheory t) = {!!}




  --   incl : ∀{a b} -> ix (⟨ T ⟩ (incl b)) a -> CtxHom (incl (incl a)) (incl b)
  --   _⋆-⧜_ : ∀{a b x} -> CtxHom a x -> CtxHom b x -> CtxHom (incl (⟨ a ⟩ ⋆ ⟨ b ⟩)) x




-- mutual
  -- infixl 29 _⋆-⧜_
  -- data Terms-𝕋× (𝑨 : 𝕋× 𝑖) : (Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) (Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) -> 𝒰 𝑖 where
  --   -- incl-Terms : 𝑒𝑙 ⟨ Γ ⟩ ⟶ (Term-𝕋× 𝑨 Δ) -> Terms-𝕋× 𝑨 Γ Δ

  --   ◌-⧜ : ∀{Γ} -> Terms-𝕋× 𝑨 ⊥ Γ
  --   _⋆-⧜_ : ∀{Γ α β} -> Terms-𝕋× 𝑨 α Γ -> Terms-𝕋× 𝑨 β Γ -> Terms-𝕋× 𝑨 (α ⊔ β) Γ
  --   incl : ∀{Γ s} -> Term₁-𝕋× 𝑨 ⟨ Γ ⟩ s -> Terms-𝕋× 𝑨 (incl (incl s)) Γ


data Term₁-𝕋× (a : 𝕋× 𝑖) : (Γ : 人List (Type-𝕋× a)) (τ : Type-𝕋× a) -> 𝒰 𝑖 where
  var : ∀{τ Γ} -> Γ ∍ τ -> Term₁-𝕋× a Γ τ
  con : ∀{Γ αs α} -> (c : Con a αs α) -> CtxHom (Term₁-𝕋× a) ((ι αs)) (Γ) -> Term₁-𝕋× a Γ α
    -- con : ∀{Γ αs α} -> (c : Con a αs α) -> Terms-𝕋× a (incl (ι αs)) (incl Γ) -> Term₁-𝕋× a Γ α


Term-𝕋× : (a : 𝕋× 𝑖) -> (𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× a)) -> (𝐈𝐱 (Type-𝕋× a) (𝐔𝐧𝐢𝐯 𝑖))
Term-𝕋× a Γ = indexed (λ τ → Term₁-𝕋× a ⟨ Γ ⟩ τ)

Terms-𝕋× : (𝑨 : 𝕋× 𝑖) -> (Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) -> (Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) -> 𝒰 𝑖
Terms-𝕋× 𝑨 Γ Δ = CtxHom (Term₁-𝕋× 𝑨) ⟨ Γ ⟩ ⟨ Δ ⟩

分Term = Term₁-𝕋×

全Term = Terms-𝕋×




